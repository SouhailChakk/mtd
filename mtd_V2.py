"""
Moving Target Defense Ryu controller with dynamic VIP rotation and reply locking.

Rewritten from scratch to preserve legacy logging semantics while adding
per-packet randomized outbound VIP selection, reply VIP locking, and
comprehensive housekeeping.

DNS resolution integrated: hostnames resolve to primary VIPs.
"""

import json
import random
import socket
import struct
from dataclasses import dataclass, field
from time import time
from typing import Dict, List, Optional, Set, Tuple

from ryu.base import app_manager
from ryu.controller import event, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, set_ev_cls
from ryu.lib import hub
from ryu.lib.packet import arp, ethernet, icmp, ipv4, packet, tcp, udp
from ryu.ofproto import ofproto_v1_3


SessionKey = Tuple[str, str, int, int, int]


@dataclass
class SessionRecord:
    key: SessionKey
    datapath: "ryu.controller.controller.Datapath"
    created: float
    last_growth: float
    packet_count: int = 0
    last_reported_count: int = 0
    vip_src: Optional[str] = None
    vip_dst: Optional[str] = None
    vip_locked: Optional[str] = None
    last_reply_vip: Optional[str] = None
    last_contacted_vip: Optional[str] = None
    last_vip_src_use: float = 0.0
    last_vip_src_announce: float = 0.0
    active_target_vip: Optional[str] = None
    vip_src_by_target: Dict[str, str] = field(default_factory=dict)
    src_ip_initial: str = ""
    dst_ip_initial: str = ""
    reverse_src_initial: str = ""
    reverse_dst_initial: str = ""
    proto: int = 0
    reply_keys: Set[Tuple] = field(default_factory=set)


class EventMessage(event.EventBase):
    def __init__(self, message: str):
        super(EventMessage, self).__init__()
        self.msg = message


class MovingTargetDefense(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _EVENTS = [EventMessage]

    # ===================== CONFIG =====================
    NUM_VIPS = 244                   # VIP pool size (addresses from 10.0.0.11-10.0.0.254)
    VIP_ROTATION_INTERVAL = 60       # rotate primary VIP after this many seconds of activity
    SESSION_NO_GROWTH_TIMEOUT = 5   # session "quiet" threshold (s)
    HOUSEKEEPING_INTERVAL = 15        # periodic tick (s)
    DISCOVERY_RANGE_LAST_OCTET_MAX = 10   # discover 10.0.0.1..10.0.0.10
    VIP_POOL_START = "10.0.0.11"         # first VIP (avoid clashing with discovered hosts)

    INITIAL_ASSIGN_ON_DISCOVERY = True

    ICMP_INSTALL_FLOWS = False
    ICMP_FLOW_IDLE = 5
    
    # DNS config
    DNS_SERVER_PORT = 53
    DNS_TTL = 300  # 5 minutes
    # ==================================================

    def __init__(self, *args, **kwargs):
        super(MovingTargetDefense, self).__init__(*args, **kwargs)

        # dataplanes & L2 learn
        self.mac_to_port: Dict[int, Dict[str, int]] = {}
        self.datapaths: Set["ryu.controller.controller.Datapath"] = set()

        # hosts (real)
        self.detected_hosts: Set[str] = set()
        self.HostAttachments: Dict[str, int] = {}
        self.host_ip_to_mac: Dict[str, str] = {}
        self.host_mac_to_ip: Dict[str, str] = {}
        # Hostname to real IP mapping (h1 -> 10.0.0.1, h2 -> 10.0.0.2, etc.)
        self.hostname_to_real_ip: Dict[str, str] = {}
        self.real_ip_to_hostname: Dict[str, str] = {}

        # VIP state
        self.V2R_Mappings: Dict[str, str] = {}
        self.host_vip_pools: Dict[str, Set[str]] = {}
        self.vip_mac_map: Dict[str, str] = {}
        self.vip_created_at: Dict[str, float] = {}
        self.vip_last_seen: Dict[str, float] = {}
        self.vip_last_activity: Dict[str, float] = {}
        self.vip_active_sessions: Dict[str, Set[SessionKey]] = {}

        # reply VIP binding (legacy logging expectations)
        self.reply_vip_pair: Dict[Tuple[str, str, int], str] = {}
        self._reply_vip_by_5tuple: Dict[Tuple[str, str, int, int, int], str] = {}
        self.session_last_contacted_vip: Dict[Tuple[str, str, int, int, int], str] = {}

        # ICMP echo tracking so replies map back to the VIP that was contacted
        # even when multiple outstanding requests target different VIPs.
        self.icmp_echo_map: Dict[Tuple[str, str, int, int], Tuple[str, float]] = {}

        # Active session tracking per real host to support dynamic VIP scaling.
        self.host_active_sessions: Dict[str, Set[SessionKey]] = {}

        # VIP resource pool
        self.Resources: List[str] = self._generate_vips(self.VIP_POOL_START, self.NUM_VIPS)

        # sessions: session_table[key] -> SessionRecord
        self.session_table: Dict[SessionKey, SessionRecord] = {}

        # current primary VIP per host (latest assigned address)
        # NEW: Single primary VIP per host per rotation window
        self.host_primary_vip: Dict[str, Optional[str]] = {}
        self.host_primary_assigned_at: Dict[str, float] = {}
        self.host_primary_active_since: Dict[str, float] = {}
        # Track when primary VIP was last active (for grace period logic)
        self.host_primary_ever_active: Dict[str, bool] = {}
        # Track last activity time for primary VIP to detect if it was active throughout rotation
        self.host_primary_last_activity: Dict[str, float] = {}

    # ---------------- lifecycle ----------------
    def start(self):
        super(MovingTargetDefense, self).start()
        self.threads.append(hub.spawn(self._ticker))
        self._initialize_hostname_mapping()

    def _initialize_hostname_mapping(self):
        """Initialize hostname to IP mapping (h1->10.0.0.1, h2->10.0.0.2, etc.)"""
        for i in range(1, self.DISCOVERY_RANGE_LAST_OCTET_MAX + 1):
            ip = f"10.0.0.{i}"
            hostname = f"h{i}"
            self.hostname_to_real_ip[hostname] = ip
            self.real_ip_to_hostname[ip] = hostname

    def _ticker(self):
        while True:
            try:
                self.send_event_to_observers(EventMessage("TICK"))
            except Exception as e:  # pragma: no cover - defensive log
                self.logger.error("Ticker exception: %s", e)
            hub.sleep(self.HOUSEKEEPING_INTERVAL)

    # ---------------- utils ----------------
    def _generate_vips(self, start_ip: str, count: int) -> List[str]:
        base = list(map(int, start_ip.split('.')))
        out: List[str] = []
        for _ in range(count):
            out.append('.'.join(map(str, base)))
            base[3] += 1
            for i in (3, 2, 1):
                if base[i] > 255:
                    base[i] = 0
                    base[i - 1] += 1
        return out

    def _generate_vip_mac(self, vip_ip: str) -> str:
        o = [int(x) for x in vip_ip.split('.')]
        return "02:%02x:%02x:%02x:%02x:%02x" % (
            (o[0] ^ 0xAA) & 0xFF,
            (o[1] ^ 0x55) & 0xFF,
            o[2],
            o[3],
            (o[2] ^ o[3]) & 0xFF,
        )

    def _touch_vip(self, vip: str, ts: float, reason: str = "") -> None:
        if not vip:
            return
        self.vip_last_seen[vip] = ts
        self.vip_last_activity[vip] = ts
        # Mark primary VIP as active if it's the current primary
        owner = self.V2R_Mappings.get(vip)
        if owner and self.host_primary_vip.get(owner) == vip:
            self.host_primary_ever_active[owner] = True

    def _detach_session_from_vip(self, vip: Optional[str], session_key: SessionKey) -> bool:
        if not vip:
            return False
        active = self.vip_active_sessions.get(vip)
        if not active:
            return True
        active.discard(session_key)
        if not active:
            self.vip_active_sessions.pop(vip, None)
            owner = self.V2R_Mappings.get(vip)
            if owner and self.host_primary_vip.get(owner) == vip:
                self.host_primary_active_since.pop(owner, None)
            return True
        return False

    def _activate_vip_for_session(self, vip: Optional[str], session_key: SessionKey, ts: float) -> None:
        if not vip:
            return
        sessions = self.vip_active_sessions.setdefault(vip, set())
        if session_key in sessions:
            return
        was_empty = not sessions
        sessions.add(session_key)
        owner = self.V2R_Mappings.get(vip)
        if was_empty and owner and self.host_primary_vip.get(owner) == vip:
            self.host_primary_active_since[owner] = ts
            self.host_primary_ever_active[owner] = True

    # ---------------- switch bringup ----------------
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):
        dp = ev.msg.datapath
        self.datapaths.add(dp)
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofp.OFPP_CONTROLLER, ofp.OFPCML_NO_BUFFER)]
        self._add_flow(dp, priority=0, match=match, actions=actions)
        self.logger.info("[SW] Switch %016x connected; installed table-miss", dp.id)

    def _add_flow(self, dp, priority, match, actions, buffer_id=None, hard_timeout=0, idle_timeout=60):
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        inst = [parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions)]
        if buffer_id is not None:
            mod = parser.OFPFlowMod(datapath=dp,
                                    buffer_id=buffer_id,
                                    priority=priority,
                                    match=match,
                                    instructions=inst,
                                    hard_timeout=hard_timeout,
                                    idle_timeout=idle_timeout)
        else:
            mod = parser.OFPFlowMod(datapath=dp,
                                    priority=priority,
                                    match=match,
                                    instructions=inst,
                                    hard_timeout=hard_timeout,
                                    idle_timeout=idle_timeout)
        dp.send_msg(mod)

    # ---------------- housekeeping ----------------
    @set_ev_cls(EventMessage)
    def _housekeeping(self, _):
        now = time()

        # 1) poll sessions via virtual growth accounting
        total = 0
        for session_key, session in list(self.session_table.items()):
            total += 1
            if session.packet_count > session.last_reported_count:
                delta = session.packet_count - session.last_reported_count
                session.last_reported_count = session.packet_count
                session.last_growth = now
                src_ip = session.src_ip_initial or session.key[0]
                dst_ip = session.dst_ip_initial or session.key[1]
                self.logger.info("STATS: growth %s -> %s (+%d) pkts=%d",
                                 src_ip, dst_ip, delta, session.packet_count)
                if session.vip_dst:
                    self._touch_vip(session.vip_dst, now, "stats growth: vip_dst")
                if session.vip_src:
                    self._touch_vip(session.vip_src, now, "stats growth: vip_src")
            else:
                age = now - session.last_growth
                if age > self.SESSION_NO_GROWTH_TIMEOUT:
                    src_ip = session.src_ip_initial or session.key[0]
                    dst_ip = session.dst_ip_initial or session.key[1]
                    self.logger.info("SESSION: drop %s -> %s (%.1fs no growth)",
                                     src_ip, dst_ip, age)
                    self._finalize_session(session_key, now, reason="session drop")

        self.logger.info("STATS: polled %d sessions", total)

        # Update idle timers for all VIPs
        # Ensure vip_last_seen tracks the last time packets were seen for each VIP
        # For VIPs with active sessions, last_seen is updated via _touch_vip on packet activity
        # For VIPs without active sessions, we ensure last_seen reflects last activity
        for vip in list(self.V2R_Mappings.keys()):
            sessions = self.vip_active_sessions.get(vip)
            if not sessions:
                # VIP has no active sessions - ensure last_seen reflects last activity
                # If last_activity exists and is more recent than last_seen, update it
                last_activity = self.vip_last_activity.get(vip)
                if last_activity and last_activity > self.vip_last_seen.get(vip, 0):
                    self.vip_last_seen[vip] = last_activity
                # If neither exists, set to created_at
                elif vip not in self.vip_last_seen:
                    self.vip_last_seen[vip] = self.vip_created_at.get(vip, now)
                    self.vip_last_activity[vip] = self.vip_created_at.get(vip, now)
                # Idle time = now - last_seen (will increment each housekeeping cycle for idle VIPs)

        # 2) evaluate each host for rotation and cleanup (NEW LOGIC)
        for real_ip in list(self.detected_hosts):
            self._evaluate_host_state(real_ip, now)

        # 3) proactive (light) discovery
        self._proactive_discovery(now)

        # 4) prune stale ICMP echo bindings so the map does not grow without bound
        icmp_expiry = self.SESSION_NO_GROWTH_TIMEOUT * 4
        for key, (vip, ts) in list(self.icmp_echo_map.items()):
            if (now - ts) > icmp_expiry:
                self.icmp_echo_map.pop(key, None)

        # 5) log snapshot
        self._log_vip_pools(now)

    def _evaluate_host_state(self, real_ip: str, now: float) -> None:
        """
        ROTATION LOGIC:
        - Each primary VIP gets 60s grace period to become active
        - If primary has active sessions during those 60s, it stays as primary
        - After 60s: if primary was ever active OR has active sessions:
            → Assign NEW primary VIP for new sessions
            → Old primary stays active until its sessions end, then dropped immediately
        - After 60s: if primary was NEVER active → drop it immediately, assign new primary
        - Old primary VIPs are dropped immediately when they lose all sessions
        """
        primary = self.host_primary_vip.get(real_ip)
        assigned_at = self.host_primary_assigned_at.get(real_ip, now)
        
        # Initialize if needed
        if primary is None:
            if self.host_active_sessions.get(real_ip):
                # Host has active sessions but no primary - assign one
                self._ensure_primary_vip(real_ip, now, force=True)
            return

        # Check if we need to rotate (after 60s grace period)
        time_since_assignment = now - assigned_at
        
        if time_since_assignment >= self.VIP_ROTATION_INTERVAL:
            # 60s grace period expired - now evaluate
            ever_active = self.host_primary_ever_active.get(real_ip, False)
            has_active_sessions = bool(self.vip_active_sessions.get(primary))
            
            if ever_active or has_active_sessions:
                # Primary was active during the 60s OR still has active sessions
                # Assign new primary for NEW sessions
                # Old primary keeps its sessions until they end
                self.logger.info("ROTATE: host %s primary VIP was active (ever=%s, has_sessions=%s), assigning new primary (old=%s)",
                                 real_ip, ever_active, has_active_sessions, primary)
                old_primary = primary  # Remember old primary
                new_primary = self._allocate_vip_to_host(real_ip, now, announce=True, make_primary=True)
                if new_primary:
                    # Ensure assigned_at is set correctly for new primary
                    self.host_primary_assigned_at[real_ip] = now
                    self.host_primary_active_since.pop(real_ip, None)
                    self.host_primary_ever_active[real_ip] = False  # Reset for new primary
                    self.host_primary_last_activity[real_ip] = now
                    # Old primary is demoted from primary but keeps its sessions
                    # Sessions remain in vip_active_sessions[old_primary]
                    # New sessions will use new_primary
                    # CRITICAL: Immediately send additional ARP updates to ensure all hosts know about new VIP
                    # This prevents ARP cache misses and ping delays during rotation
                    # (announce=True already sends ARP, but we send again to ensure immediate propagation)
                    self._send_gratuitous_arp_to_all(new_primary)
                    self._send_targeted_arp_updates(new_primary)
                    self.logger.info("ROTATE: host %s new primary=%s (old=%s keeps %d sessions until they end)",
                                     real_ip, new_primary, old_primary, 
                                     len(self.vip_active_sessions.get(old_primary, set())))
                    return
            else:
                # Primary was NEVER active during the 60s grace period - drop it
                self.logger.info("ROTATE: host %s primary VIP %s never active during 60s grace, dropping",
                                 real_ip, primary)
                self._reclaim_vip(primary, rebalance=False)
                # Assign new primary (may be same VIP if it was just reclaimed)
                new_primary = self._ensure_primary_vip(real_ip, now, force=True)
                if new_primary:
                    # Ensure assigned_at is set correctly for new primary
                    self.host_primary_assigned_at[real_ip] = now
                    self.host_primary_active_since.pop(real_ip, None)
                    self.host_primary_ever_active[real_ip] = False  # Reset for new primary
                    self.host_primary_last_activity[real_ip] = now
                    # CRITICAL: Immediately send ARP updates MULTIPLE times to ensure all hosts know about new VIP
                    # This is especially important when VIP is immediately reassigned after reclaim
                    # Send ARP aggressively to prevent ARP cache misses and ping delays
                    for _ in range(2):  # Send twice to ensure propagation
                        self._send_gratuitous_arp_to_all(new_primary)
                        self._send_targeted_arp_updates(new_primary)
                    return
        else:
            # Still within 60s grace period - don't check anything, just wait
            # Primary VIP has time to become active
            pass
        
        # Clean up old non-primary VIPs that no longer have sessions
        # IMPORTANT: Only reclaim VIPs that have NO active sessions
        # Old primary VIPs will keep their sessions until they end
        pool = self.host_vip_pools.get(real_ip, set())
        current_primary = self.host_primary_vip.get(real_ip)
        for vip in list(pool):
            if vip == current_primary:
                continue  # Skip current primary
            active_sessions = self.vip_active_sessions.get(vip)
            if not active_sessions:  # No active sessions
                # Old VIP with no sessions - reclaim it immediately
                self.logger.info("CLEANUP: reclaiming old VIP %s from host %s (no active sessions)",
                                vip, real_ip)
                self._reclaim_vip(vip, rebalance=False)
            else:
                # Old VIP still has active sessions - keep it
                self.logger.debug("CLEANUP: keeping old VIP %s from host %s (%d active sessions)",
                                 vip, real_ip, len(active_sessions))

    def _ensure_primary_vip(self, real_ip: str, now: float, *, force: bool = False) -> Optional[str]:
        """Ensure host has a primary VIP. Returns the primary VIP."""
        pool = self.host_vip_pools.setdefault(real_ip, set())
        primary = self.host_primary_vip.get(real_ip)

        if primary and primary in pool:
            return primary

        if not force and not self.host_active_sessions.get(real_ip):
            return None

        # Allocate new primary VIP
        vip = self._allocate_vip_to_host(real_ip, now, announce=True, make_primary=True)
        if vip:
            self.host_primary_assigned_at[real_ip] = now
            self.host_primary_active_since.pop(real_ip, None)
            self.host_primary_ever_active[real_ip] = False  # Reset for new primary
        return vip

    def _take_resource_vip(self, now: float) -> Optional[str]:
        if not self.Resources:
            return None
        return self.Resources.pop(0)

    def _rotate_host_vip(self, real_ip: str, now: float) -> None:
        """Legacy method - kept for compatibility but logic is in _evaluate_host_state"""
        self._evaluate_host_state(real_ip, now)

    def _bind_vip_to_host(self, vip: str, real_ip: str, now: float, *, make_primary: bool = False) -> None:
        # Check if VIP was previously assigned (even if just reclaimed)
        # If VIP exists in V2R_Mappings, it means it's being reassigned without reclaim
        old_owner = self.V2R_Mappings.get(vip)
        if old_owner and old_owner != real_ip:
            # VIP is being reassigned to a different host - purge old flows
            self._purge_flows_for_vip(vip)
        # Note: If VIP was reclaimed, flows were already purged in _reclaim_vip
        # But we still need to ensure flows are clean for immediate reassignment
        
        self.V2R_Mappings[vip] = real_ip
        self.host_vip_pools.setdefault(real_ip, set()).add(vip)
        self.vip_created_at[vip] = now
        self.vip_last_seen[vip] = now
        self.vip_last_activity[vip] = now
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
        if make_primary or self.host_primary_vip.get(real_ip) is None:
            self.host_primary_vip[real_ip] = vip
            self.host_primary_assigned_at[real_ip] = now
            self.host_primary_active_since.pop(real_ip, None)
            self.host_primary_ever_active[real_ip] = False  # New primary starts as not active
            self.host_primary_last_activity[real_ip] = now

    # ---------------- DNS resolution ----------------
    def _parse_dns_query(self, data: bytes) -> Optional[Tuple[int, str, int]]:
        """Parse DNS query from UDP payload. Returns (transaction_id, qname, qtype) or None."""
        if len(data) < 12:  # DNS header is 12 bytes
            return None
        
        # Parse DNS header
        trans_id = struct.unpack('!H', data[0:2])[0]
        flags = struct.unpack('!H', data[2:4])[0]
        
        # Check if it's a query (QR=0)
        if (flags & 0x8000) != 0:  # QR bit set = response
            return None
        
        qdcount = struct.unpack('!H', data[4:6])[0]
        if qdcount == 0:
            return None
        
        # Parse question section
        offset = 12
        qname_parts = []
        while offset < len(data) and data[offset] != 0:
            length = data[offset]
            if length == 0 or offset + length >= len(data):
                return None
            offset += 1
            qname_parts.append(data[offset:offset+length].decode('utf-8', errors='ignore'))
            offset += length
        
        if offset >= len(data) - 4:
            return None
        
        offset += 1  # Skip null terminator
        qtype = struct.unpack('!H', data[offset:offset+2])[0]
        qname = '.'.join(qname_parts).lower().rstrip('.')
        
        return (trans_id, qname, qtype)

    def _build_dns_response(self, trans_id: int, qname: str, answer_ip: str, qtype: int) -> bytes:
        """Build DNS response packet with A record."""
        # DNS header
        flags = 0x8180  # QR=1, AA=1, RD=1, RA=0, rcode=0
        header = struct.pack('!HHHHHH',
                             trans_id,
                             flags,
                             1,  # QDCOUNT = 1
                             1,  # ANCOUNT = 1
                             0,  # NSCOUNT = 0
                             0)  # ARCOUNT = 0
        
        # Question section
        qname_parts = qname.split('.')
        question = b''
        for part in qname_parts:
            question += struct.pack('!B', len(part)) + part.encode('utf-8')
        question += b'\x00'  # null terminator
        question += struct.pack('!HH', qtype if qtype == 1 else 1, 1)  # QTYPE, QCLASS (1=A, 1=IN)
        
        # Answer section
        # Name pointer to question (0xC000 = pointer to offset 0x00 in question)
        answer = struct.pack('!H', 0xC00C)  # Pointer to question name
        answer += struct.pack('!H', 1)      # TYPE = A (1)
        answer += struct.pack('!H', 1)      # CLASS = IN (1)
        answer += struct.pack('!I', self.DNS_TTL)  # TTL
        answer += struct.pack('!H', 4)      # RDLENGTH = 4 bytes
        answer += socket.inet_aton(answer_ip)  # RDATA = IP address
        
        return header + question + answer

    def _handle_dns_query(self, pkt: packet.Packet, dp, in_port, eth, ip4, raw_data: bytes = None) -> bool:
        """Handle DNS queries and respond with VIP mappings."""
        udp_pkt = pkt.get_protocol(udp.udp)
        
        if not udp_pkt:
            return False
            
        # Only handle DNS queries (port 53)
        if udp_pkt.dst_port != self.DNS_SERVER_PORT:
            return False
        
        # Get UDP payload - extract from packet data
        if raw_data:
            pkt_data = raw_data
        else:
            # Try to get from packet's serialized data
            try:
                pkt.serialize()
                pkt_data = bytes(pkt.data) if hasattr(pkt, 'data') else None
            except:
                pkt_data = None
        
        if not pkt_data:
            return False
        
        # Find UDP payload - skip Ethernet (14) + IP header (variable) + UDP header (8)
        eth_len = 14
        ip_header_len = (ip4.header_length * 4) if hasattr(ip4, 'header_length') else 20
        udp_offset = eth_len + ip_header_len + 8
        
        if len(pkt_data) <= udp_offset:
            return False
        
        udp_data = pkt_data[udp_offset:]
        
        if not udp_data or len(udp_data) < 12:
            return False
        
        # Parse DNS query
        parsed = self._parse_dns_query(udp_data)
        if not parsed:
            return False
        
        trans_id, qname, qtype = parsed
        
        self.logger.info("DNS: query for %s (type=%d) from %s", qname, qtype, ip4.src)
        
        # Check if query is for a known hostname
        if qname in self.hostname_to_real_ip:
            real_ip = self.hostname_to_real_ip[qname]
            
            # Get primary VIP for this host
            primary_vip = self.host_primary_vip.get(real_ip)
            
            if not primary_vip:
                # No primary VIP yet - assign one
                now = time()
                primary_vip = self._ensure_primary_vip(real_ip, now, force=True)
            
            if primary_vip:
                # Respond with VIP
                self._send_dns_response(dp, eth, ip4, udp_pkt, trans_id, qname, primary_vip, qtype)
                self.logger.info("DNS: resolved %s -> %s (VIP %s)", qname, real_ip, primary_vip)
                return True
        
        # Unknown hostname - don't handle (let it pass through)
        return False

    def _send_dns_response(self, dp, eth, ip4, udp_pkt, trans_id: int, qname: str, answer_ip: str, qtype: int):
        """Send DNS response with A record pointing to VIP."""
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        
        # Build DNS response payload
        dns_response_data = self._build_dns_response(trans_id, qname, answer_ip, qtype)
        
        # Build UDP packet
        udp_response = udp.udp(
            src_port=udp_pkt.dst_port,
            dst_port=udp_pkt.src_port,
            total_length=8 + len(dns_response_data),
            csum=0
        )
        
        # Build IP packet
        ip_response = ipv4.ipv4(
            version=4,
            header_length=5,
            tos=0,
            total_length=20 + 8 + len(dns_response_data),
            identification=0,
            flags=0,
            offset=0,
            ttl=64,
            proto=17,  # UDP
            csum=0,
            src=ip4.dst,
            dst=ip4.src
        )
        
        # Build Ethernet frame
        eth_response = ethernet.ethernet(
            dst=eth.src,
            src=eth.dst,
            ethertype=eth.ethertype
        )
        
        # Serialize
        p = packet.Packet()
        p.add_protocol(eth_response)
        p.add_protocol(ip_response)
        p.add_protocol(udp_response)
        p.data = dns_response_data  # Add DNS payload
        p.serialize()
        
        # Get output port
        out_port = self.mac_to_port.get(dp.id, {}).get(eth.src, ofp.OFPP_FLOOD)
        
        # Send packet out
        actions = [parser.OFPActionOutput(out_port)]
        dp.send_msg(parser.OFPPacketOut(
            datapath=dp,
            buffer_id=ofp.OFP_NO_BUFFER,
            in_port=ofp.OFPP_CONTROLLER,
            actions=actions,
            data=p.data
        ))

    # ---------------- packet-in ----------------
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in(self, ev):
        msg = ev.msg
        dp = msg.datapath
        ofp = dp.ofproto
        parser = dp.ofproto_parser
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocol(ethernet.ethernet)
        if not eth:
            return

        dpid = dp.id
        self.mac_to_port.setdefault(dpid, {})
        self.mac_to_port[dpid][eth.src] = in_port

        # learn hosts early
        self._learn_host(pkt, dpid)

        actions: List = []
        out_port = ofp.OFPP_FLOOD
        forward_dst_mac: Optional[str] = None

        # ---- IPv4 ----
        ip4 = pkt.get_protocol(ipv4.ipv4)
        if ip4:
            # Handle DNS queries first
            if self._handle_dns_query(pkt, dp, in_port, eth, ip4, raw_data=bytes(msg.data)):
                return  # DNS handled, don't process further
        
        # ---- ARP ----
        a = pkt.get_protocol(arp.arp)
        if a and a.opcode == arp.ARP_REQUEST:
            dip, sip, smac = a.dst_ip, a.src_ip, a.src_mac

            # Lazy-assign unowned VIPs so they always answer
            if (dip.startswith("10.0.0.") and
                dip not in self.V2R_Mappings and
                dip in self.Resources):
                now = time()
                if self.detected_hosts:
                    target = min(self.detected_hosts,
                                 key=lambda h: len(self.host_vip_pools.get(h, set())))
                    try:
                        self.Resources.remove(dip)
                        self.V2R_Mappings[dip] = target
                        self.host_vip_pools.setdefault(target, set()).add(dip)
                        self.vip_created_at[dip] = now
                        self.vip_mac_map[dip] = self._generate_vip_mac(dip)
                        self._purge_flows_for_vip(dip)
                        self._send_gratuitous_arp_to_all(dip)
                        self._send_targeted_arp_updates(dip)
                        self.logger.info("LAZY-ASSIGN: VIP %s -> %s on ARP from %s", dip, target, sip)
                    except ValueError:
                        pass

            if dip in self.V2R_Mappings:
                mac = self.vip_mac_map.get(dip) or self._generate_vip_mac(dip)
                self.vip_mac_map[dip] = mac
                self._send_arp_reply(dp, eth.ethertype, eth.src, mac, dip, smac, sip, in_port)
                self.logger.info("ARP: replied VIP %s -> %s", dip, mac)
                return
            if dip in self.host_ip_to_mac:
                mac = self.host_ip_to_mac[dip]
                self._send_arp_reply(dp, eth.ethertype, eth.src, mac, dip, smac, sip, in_port)
                self.logger.info("ARP: replied real %s -> %s", dip, mac)
                return

        # ---- IPv4 (continued) ----
        if not ip4:
            return

        tcp_pkt = pkt.get_protocol(tcp.tcp)
        udp_pkt = pkt.get_protocol(udp.udp)
        icmp_pkt = pkt.get_protocol(icmp.icmp)

        src_ip, dst_ip, proto = ip4.src, ip4.dst, ip4.proto
        src_port = tcp_pkt.src_port if tcp_pkt else (udp_pkt.src_port if udp_pkt else 0)
        dst_port = tcp_pkt.dst_port if tcp_pkt else (udp_pkt.dst_port if udp_pkt else 0)
        now = time()

        direction, session_key, client_real, server_real, client_port, server_port = \
            self._classify_flow(src_ip, dst_ip, proto, src_port, dst_port)

        session = self.session_table.get(session_key)
        new_session = False
        if not session:
            session = self._create_session_record(session_key, dp, now,
                                                   src_ip, dst_ip, proto)
            self.session_table[session_key] = session
            new_session = True
            affected_hosts: Set[str] = set()
            for host in (server_real, client_real):
                if host not in self.detected_hosts:
                    continue
                host_sessions = self.host_active_sessions.setdefault(host, set())
                host_sessions.add(session_key)
                affected_hosts.add(host)
            for host in affected_hosts:
                self._evaluate_host_state(host, now)
                # Ensure primary VIP exists for new sessions
                self._ensure_primary_vip(host, now, force=True)

        vip_dst = None
        forward_dst_mac = None

        # NEW LOGIC: For forward direction, use existing VIP or primary VIP of destination
        if direction == 'forward':
            # CRITICAL: If dst_ip is already a VIP, use that VIP directly (user explicitly pinged it)
            # This ensures that when you ping a specific VIP, that VIP is used for the session
            if dst_ip in self.V2R_Mappings and self.V2R_Mappings.get(dst_ip) == server_real:
                # User explicitly pinged this VIP - use it
                vip_dst = dst_ip
                # Ensure this VIP is in the session
                if not session.vip_dst or session.vip_dst != vip_dst:
                    session.vip_dst = vip_dst
            elif session.vip_dst and self.V2R_Mappings.get(session.vip_dst) == server_real:
                # Session already has a VIP assigned - use it (preserves old primary VIP sessions)
                vip_dst = session.vip_dst
            else:
                # New session or VIP no longer valid - use current primary VIP
                primary_dst_vip = self._ensure_primary_vip(server_real, now, force=True)
                if primary_dst_vip:
                    vip_dst = primary_dst_vip
                    # For new sessions, immediately send ARP update to client to prevent delays
                    # This is especially important for ICMP ping continuity during rotation
                    if new_session:
                        self._send_targeted_arp_to_host_for_vip(vip_dst, client_real)
            
            if vip_dst:
                real_dst = server_real
                actions.append(parser.OFPActionSetField(ipv4_dst=real_dst))
                dst_mac = self.host_ip_to_mac.get(real_dst)
                if dst_mac:
                    actions.append(parser.OFPActionSetField(eth_dst=dst_mac))
                    forward_dst_mac = dst_mac
                session.vip_dst = vip_dst
                session.last_contacted_vip = vip_dst
                if proto != 1 and not session.vip_locked:
                    session.vip_locked = vip_dst
                self._touch_vip(vip_dst, now, "session create: vip_dst")
                if new_session:
                    self._activate_vip_for_session(vip_dst, session_key, now)
                else:
                    # Reactivate for existing session to ensure it stays attached
                    self._activate_vip_for_session(vip_dst, session_key, now)
                self._register_reply_mapping(session, server_real, client_real,
                                             proto, vip_dst, client_port, server_port,
                                             icmp_pkt, tcp_pkt, udp_pkt)
                if (icmp_pkt and getattr(icmp_pkt, "type", None) == 8 and
                        hasattr(icmp_pkt, "data")):
                    echo_id = getattr(icmp_pkt.data, "id", None)
                    echo_seq = getattr(icmp_pkt.data, "seq", None)
                    if echo_id is not None and echo_seq is not None:
                        key = (server_real, client_real, int(echo_id), int(echo_seq))
                        self.icmp_echo_map[key] = (vip_dst, now)
                if vip_dst:
                    flow_key = (client_real, server_real, proto, client_port, server_port)
                    self.session_last_contacted_vip[flow_key] = vip_dst

        # NEW LOGIC: For forward direction, use existing VIP or primary VIP of source
        if direction == 'forward':
            # For existing sessions, use their already-assigned VIP
            # For new sessions, use primary VIP
            if session.vip_src and self.V2R_Mappings.get(session.vip_src) == client_real:
                # Session already has a VIP assigned - use it (preserves old primary VIP sessions)
                vip_src = session.vip_src
            else:
                # New session or VIP no longer valid - use current primary VIP
                primary_src_vip = self._ensure_primary_vip(client_real, now, force=True)
                if primary_src_vip:
                    vip_src = primary_src_vip
                else:
                    vip_src = None
            
            if vip_src:
                session.vip_src = vip_src
                session.active_target_vip = vip_dst
                if vip_dst:
                    session.vip_src_by_target[vip_dst] = vip_src
                session.last_vip_src_use = now
                if new_session:
                    session.last_vip_src_announce = 0.0
                self._activate_vip_for_session(vip_src, session_key, now)
                self._touch_vip(vip_src, now, "session create: vip_src")
                if new_session or (now - session.last_vip_src_announce) >= self.SESSION_NO_GROWTH_TIMEOUT:
                    self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
                    session.last_vip_src_announce = now
                self._evaluate_host_state(client_real, now)
                
                mac = self.vip_mac_map.get(vip_src) or self._generate_vip_mac(vip_src)
                self.vip_mac_map[vip_src] = mac
                actions.append(parser.OFPActionSetField(ipv4_src=vip_src))
                actions.append(parser.OFPActionSetField(eth_src=mac))
            
            if not forward_dst_mac:
                forward_dst_mac = self.host_ip_to_mac.get(server_real)

        else:  # reverse direction (server -> client)
            flow_key = (client_real, server_real, proto, client_port, server_port)
            mapping_vip = self._select_reply_vip_5tuple(server_real, client_real,
                                                        proto, client_port, server_port)
            contacted_vip = self.session_last_contacted_vip.get(flow_key)
            vip_src = None

            icmp_bound_vip: Optional[str] = None
            if proto == 1 and icmp_pkt and getattr(icmp_pkt, "type", None) == 0 and hasattr(icmp_pkt, "data"):
                echo_id = getattr(icmp_pkt.data, "id", None)
                echo_seq = getattr(icmp_pkt.data, "seq", None)
                if echo_id is not None and echo_seq is not None:
                    key = (server_real, client_real, int(echo_id), int(echo_seq))
                    stored = self.icmp_echo_map.pop(key, None)
                    if stored:
                        candidate_vip, _stored_ts = stored
                        if self.V2R_Mappings.get(candidate_vip) == server_real:
                            icmp_bound_vip = candidate_vip

            # NEW LOGIC: Prefer the primary VIP for replies (if it matches the session)
            primary_reply_vip = self.host_primary_vip.get(server_real)
            # CRITICAL: If session.vip_dst is set (from forward direction), use it for replies
            # This ensures that when you ping a specific VIP, replies come from that same VIP
            if session.vip_dst and self.V2R_Mappings.get(session.vip_dst) == server_real:
                # Session has a specific VIP assigned - use it for replies
                # This handles both: explicit VIP pings and new primary VIP sessions
                vip_src = session.vip_dst
            else:
                # No specific VIP in session - use established mappings
                # Check if this session is using the current primary VIP
                session_uses_current_primary = (session.vip_dst == primary_reply_vip)
                
                if proto == 1:
                    # ICMP: If session uses current primary, prioritize primary VIP first
                    # Otherwise, use echo map (which should have the correct VIP from forward direction)
                    if session_uses_current_primary:
                        # New session using new primary: prioritize primary VIP
                        preferred_vips: List[Optional[str]] = [primary_reply_vip, icmp_bound_vip, mapping_vip, session.last_reply_vip]
                    else:
                        # Old session using old primary: use echo map first (preserves old primary)
                        preferred_vips: List[Optional[str]] = [icmp_bound_vip, mapping_vip, primary_reply_vip, session.last_reply_vip]
                    for candidate in preferred_vips:
                        if candidate and self.V2R_Mappings.get(candidate) == server_real:
                            vip_src = candidate
                            break
                else:
                    # Non-ICMP: If session uses current primary, prioritize primary VIP first
                    if session_uses_current_primary:
                        # New session using new primary: prioritize primary VIP
                        ordered: List[Optional[str]] = [primary_reply_vip, session.vip_locked, mapping_vip,
                                                        contacted_vip, session.last_reply_vip]
                    else:
                        # Old session using old primary: use established mappings
                        ordered: List[Optional[str]] = [session.vip_locked, mapping_vip, primary_reply_vip,
                                                        contacted_vip, session.last_reply_vip]
                    for candidate in ordered:
                        if candidate and self.V2R_Mappings.get(candidate) == server_real:
                            vip_src = candidate
                            break

            if vip_src and self.V2R_Mappings.get(vip_src) != server_real:
                vip_src = None

            if not vip_src and session.vip_dst and self.V2R_Mappings.get(session.vip_dst) == server_real:
                vip_src = session.vip_dst

            if not vip_src and mapping_vip and self.V2R_Mappings.get(mapping_vip) == server_real:
                vip_src = mapping_vip

            if not vip_src and contacted_vip and self.V2R_Mappings.get(contacted_vip) == server_real:
                vip_src = contacted_vip

            if not vip_src and session.last_reply_vip and self.V2R_Mappings.get(session.last_reply_vip) == server_real:
                vip_src = session.last_reply_vip

            if not vip_src:
                # Fallback to primary VIP
                if primary_reply_vip and self.V2R_Mappings.get(primary_reply_vip) == server_real:
                    vip_src = primary_reply_vip

            if vip_src:
                previous_reply_vip = session.last_reply_vip
                if previous_reply_vip and previous_reply_vip != vip_src:
                    self._detach_session_from_vip(previous_reply_vip, session_key)
                    owner = self.V2R_Mappings.get(previous_reply_vip)
                    if owner:
                        self._evaluate_host_state(owner, now)
                if proto != 1:
                    session.vip_locked = vip_src
                self._activate_vip_for_session(vip_src, session_key, now)
                self._touch_vip(vip_src, now, "reply packet")
                mac = self.vip_mac_map.get(vip_src) or self._generate_vip_mac(vip_src)
                self.vip_mac_map[vip_src] = mac
                actions.append(parser.OFPActionSetField(ipv4_src=vip_src))
                actions.append(parser.OFPActionSetField(eth_src=mac))
                session.last_reply_vip = vip_src
                key = self._compose_reply_key(server_real, client_real, proto,
                                               client_port, server_port)
                previous = self._reply_vip_by_5tuple.get(key)
                if previous != vip_src:
                    self._reply_vip_by_5tuple[key] = vip_src
                    session.reply_keys.add(key)
                    self.reply_vip_pair[(server_real, client_real, proto)] = vip_src
                    if proto == 1:
                        self.logger.info("REPLY OVERRIDE (ICMP): Using %s for %s->%s (client=%s)",
                                         vip_src, server_real, client_real, client_real)
                    else:
                        self.logger.info("REPLY OVERRIDE: Using %s for %s->%s proto=%d",
                                         vip_src, server_real, client_real, proto)
                self._send_targeted_arp_to_host_for_vip(vip_src, client_real)
            client_mac = self.host_ip_to_mac.get(client_real)
            if client_mac:
                actions.append(parser.OFPActionSetField(eth_dst=client_mac))
                forward_dst_mac = client_mac
            if dst_ip in self.V2R_Mappings:
                real_dst = self.V2R_Mappings[dst_ip]
            else:
                real_dst = dst_ip
            actions.append(parser.OFPActionSetField(ipv4_dst=real_dst))
            session.reverse_src_initial = src_ip
            session.reverse_dst_initial = dst_ip

        if not actions:
            actions.append(parser.OFPActionOutput(ofp.OFPP_FLOOD))
            out_port = ofp.OFPP_FLOOD
        else:
            if forward_dst_mac:
                out_port = self.mac_to_port.get(dpid, {}).get(forward_dst_mac, ofp.OFPP_FLOOD)
            actions.append(parser.OFPActionOutput(out_port))

        if msg.buffer_id == ofp.OFP_NO_BUFFER:
            data = msg.data
        else:
            data = None

        out = parser.OFPPacketOut(datapath=dp,
                                   buffer_id=msg.buffer_id,
                                   in_port=in_port,
                                   actions=actions,
                                   data=data)
        dp.send_msg(out)

        if new_session:
            self.logger.info("SESSION: created %s -> %s (proto %d) vip_dst=%s (key=%s)",
                             src_ip, dst_ip, proto, session.vip_dst, (src_ip, dst_ip))

        session.packet_count += 1
        session.last_growth = now
        if session.vip_src:
            self._touch_vip(session.vip_src, now, "packet activity: vip_src")
        if session.vip_locked:
            self._touch_vip(session.vip_locked, now, "packet activity: vip_locked")
        elif session.vip_dst:
            self._touch_vip(session.vip_dst, now, "packet activity: vip_dst")

    def _classify_flow(self, src_ip: str, dst_ip: str, proto: int,
                       src_port: int, dst_port: int):
        src_real = self.V2R_Mappings.get(src_ip, src_ip)
        dst_real = self.V2R_Mappings.get(dst_ip, dst_ip)
        forward_key = (src_real, dst_real, proto, src_port, dst_port)
        reverse_key = (dst_real, src_real, proto, dst_port, src_port)
        if reverse_key in self.session_table:
            client_real = dst_real
            server_real = src_real
            client_port = dst_port
            server_port = src_port
            return 'reverse', reverse_key, client_real, server_real, client_port, server_port
        return 'forward', forward_key, src_real, dst_real, src_port, dst_port

    def _create_session_record(self, session_key: SessionKey, dp, now: float,
                               src_ip: str, dst_ip: str, proto: int) -> SessionRecord:
        return SessionRecord(key=session_key,
                             datapath=dp,
                             created=now,
                             last_growth=now,
                             src_ip_initial=src_ip,
                             dst_ip_initial=dst_ip,
                             proto=proto)

    def _finalize_session(self, session_key: SessionKey, ts: float, reason: str) -> None:
        session = self.session_table.pop(session_key, None)
        if not session:
            return
        src_ip = session.src_ip_initial or session.key[0]
        dst_ip = session.dst_ip_initial or session.key[1]
        self.logger.info("SESSION: removed %s -> %s", src_ip, dst_ip)

        client_real = session.key[0]
        server_real = session.key[1]
        affected_hosts: Set[str] = set()
        for host in {client_real, server_real}:
            host_sessions = self.host_active_sessions.get(host)
            if host_sessions and session_key in host_sessions:
                host_sessions.discard(session_key)
                if not host_sessions:
                    self.host_active_sessions.pop(host, None)
                affected_hosts.add(host)
        
        # Check if VIPs should be reclaimed after session ends
        if reason != "vip reclaim":
            for host in affected_hosts:
                if host in self.detected_hosts:
                    self._evaluate_host_state(host, ts)

        for key in session.reply_keys:
            self._reply_vip_by_5tuple.pop(key, None)
        pair_key = (session.key[1], session.key[0], session.proto)
        if self.reply_vip_pair.get(pair_key) == session.vip_locked:
            self.reply_vip_pair.pop(pair_key, None)

        processed: Set[str] = set()
        for vip in {session.vip_src, session.vip_locked, session.vip_dst, session.last_reply_vip}:
            if not vip or vip in processed:
                continue
            processed.add(vip)
            owner = self.V2R_Mappings.get(vip)
            released = self._detach_session_from_vip(vip, session_key)
            if released and owner:
                # If VIP is no longer primary, it can be reclaimed
                primary = self.host_primary_vip.get(owner)
                if vip != primary:
                    # Old non-primary VIP - check if it should be reclaimed
                    self._evaluate_host_state(owner, ts)
                else:
                    # Primary VIP - evaluate to see if it needs rotation
                    self._evaluate_host_state(owner, ts)

        flow_key = (session.key[0], session.key[1], session.proto, session.key[3], session.key[4])
        reverse_key = (session.key[1], session.key[0], session.proto, session.key[4], session.key[3])
        self.session_last_contacted_vip.pop(flow_key, None)
        self.session_last_contacted_vip.pop(reverse_key, None)

        if session.proto == 1:
            for key in list(self.icmp_echo_map.keys()):
                server_real, client_real, _, _ = key
                if server_real == session.key[1] and client_real == session.key[0]:
                    self.icmp_echo_map.pop(key, None)

    def _compose_reply_key(self, server_real: str, client_real: str,
                           proto: int, client_port: int, server_port: int) -> Tuple[str, str, int, int, int]:
        if proto == 1:
            return (server_real, client_real, 1, 0, 0)
        if proto == 6:
            return (server_real, client_real, 6, client_port, server_port)
        if proto == 17:
            return (server_real, client_real, 17, client_port, server_port)
        return (server_real, client_real, proto, client_port, server_port)

    def _register_reply_mapping(self, session: SessionRecord, server_real: str,
                                client_real: str, proto: int, vip_dst: str,
                                client_port: int, server_port: int,
                                icmp_pkt, tcp_pkt, udp_pkt) -> None:
        create_binding = False
        if icmp_pkt and getattr(icmp_pkt, "type", None) == 8:
            create_binding = True
        elif tcp_pkt:
            try:
                syn = bool(tcp_pkt.bits & 0x02)
                ack = bool(tcp_pkt.bits & 0x10)
                if syn and not ack:
                    create_binding = True
            except Exception:
                pass
        elif udp_pkt:
            create_binding = True

        if not create_binding:
            return

        self.reply_vip_pair[(server_real, client_real, proto)] = vip_dst
        key = self._compose_reply_key(server_real, client_real, proto,
                                      client_port, server_port)
        self._reply_vip_by_5tuple[key] = vip_dst
        session.reply_keys.add(key)

    # ---------------- VIP helpers ----------------
    def _allocate_vip_to_host(self, real_ip: str, now: float, announce: bool = True,
                               *, make_primary: bool = False) -> Optional[str]:
        vip = self._take_resource_vip(now)
        if not vip:
            self.logger.warning("ALLOC: No VIP resources available for host %s", real_ip)
            return None
        self._bind_vip_to_host(vip, real_ip, now, make_primary=make_primary)
        if announce:
            self._send_gratuitous_arp_to_all(vip)
            self._send_targeted_arp_updates(vip)
        self.logger.info("ALLOC: on-demand VIP %s -> %s", vip, real_ip)
        return vip

    def _purge_flows_for_vip(self, vip: str) -> None:
        for dp in list(self.datapaths):
            parser = dp.ofproto_parser
            ofp = dp.ofproto
            mod_dst = parser.OFPFlowMod(
                datapath=dp,
                table_id=ofp.OFPTT_ALL,
                command=ofp.OFPFC_DELETE,
                out_port=ofp.OFPP_ANY,
                out_group=ofp.OFPG_ANY,
                match=parser.OFPMatch(eth_type=0x0800, ipv4_dst=vip)
            )
            dp.send_msg(mod_dst)
            mod_src = parser.OFPFlowMod(
                datapath=dp,
                table_id=ofp.OFPTT_ALL,
                command=ofp.OFPFC_DELETE,
                out_port=ofp.OFPP_ANY,
                out_group=ofp.OFPG_ANY,
                match=parser.OFPMatch(eth_type=0x0800, ipv4_src=vip)
            )
            dp.send_msg(mod_src)
        self.logger.info("FLOW: purged flows for VIP %s (src & dst matches)", vip)

    def _send_gratuitous_arp_to_all(self, vip: str) -> None:
        if not self.datapaths:
            return
        mac = self.vip_mac_map.get(vip) or self._generate_vip_mac(vip)
        self.vip_mac_map[vip] = mac
        for attempt in range(3):
            for dp in list(self.datapaths):
                try:
                    parser = dp.ofproto_parser
                    ofp = dp.ofproto
                    p = packet.Packet()
                    p.add_protocol(ethernet.ethernet(ethertype=0x0806,
                                                     dst='ff:ff:ff:ff:ff:ff', src=mac))
                    p.add_protocol(arp.arp(opcode=arp.ARP_REPLY,
                                           src_mac=mac, src_ip=vip,
                                           dst_mac='ff:ff:ff:ff:ff:ff', dst_ip=vip))
                    p.serialize()
                    dp.send_msg(parser.OFPPacketOut(
                        datapath=dp,
                        buffer_id=ofp.OFP_NO_BUFFER,
                        in_port=ofp.OFPP_CONTROLLER,
                        actions=[parser.OFPActionOutput(ofp.OFPP_FLOOD)],
                        data=p.data))
                except Exception as e:
                    self.logger.debug("GARP for %s failed: %s", vip, e)
            if attempt < 2:
                hub.sleep(0.1)
        self.logger.info("GARP: announced VIP %s (MAC: %s) - 3 attempts", vip, mac)

    def _send_targeted_arp_updates(self, vip: str) -> None:
        mac = self.vip_mac_map.get(vip) or self._generate_vip_mac(vip)
        for dp in list(self.datapaths):
            parser = dp.ofproto_parser
            ofp = dp.ofproto
            for host_ip, host_mac in list(self.host_ip_to_mac.items()):
                out_port = self.mac_to_port.get(dp.id, {}).get(host_mac, ofp.OFPP_FLOOD)
                try:
                    p = packet.Packet()
                    p.add_protocol(ethernet.ethernet(ethertype=0x0806, dst=host_mac, src=mac))
                    p.add_protocol(arp.arp(opcode=arp.ARP_REPLY,
                                           src_mac=mac, src_ip=vip,
                                           dst_mac=host_mac, dst_ip=host_ip))
                    p.serialize()
                    dp.send_msg(parser.OFPPacketOut(
                        datapath=dp,
                        buffer_id=ofp.OFP_NO_BUFFER,
                        in_port=ofp.OFPP_CONTROLLER,
                        actions=[parser.OFPActionOutput(out_port)],
                        data=p.data))
                except Exception as e:
                    self.logger.debug("Targeted ARP to %s for %s failed: %s", host_ip, vip, e)
        self.logger.info("ARP: targeted updates sent for VIP %s", vip)

    def _send_targeted_arp_to_host_for_vip(self, vip: str, target_real_ip: str) -> None:
        try:
            mac = self.vip_mac_map.get(vip) or self._generate_vip_mac(vip)
            self.vip_mac_map[vip] = mac
            host_mac = self.host_ip_to_mac.get(target_real_ip)
            if not host_mac:
                return
            for dp in list(self.datapaths):
                parser = dp.ofproto_parser
                ofp = dp.ofproto
                out_port = self.mac_to_port.get(dp.id, {}).get(host_mac, ofp.OFPP_FLOOD)
                p = packet.Packet()
                p.add_protocol(ethernet.ethernet(ethertype=0x0806, dst=host_mac, src=mac))
                p.add_protocol(arp.arp(opcode=arp.ARP_REPLY,
                                       src_mac=mac, src_ip=vip,
                                       dst_mac=host_mac, dst_ip=target_real_ip))
                p.serialize()
                dp.send_msg(parser.OFPPacketOut(
                    datapath=dp,
                    buffer_id=ofp.OFP_NO_BUFFER,
                    in_port=ofp.OFPP_CONTROLLER,
                    actions=[parser.OFPActionOutput(out_port)],
                    data=p.data))
            self.logger.info("ARP: targeted JIT for SNAT VIP %s -> host %s", vip, target_real_ip)
        except Exception as e:
            self.logger.warning("ARP: targeted JIT failed for %s->%s: %s", vip, target_real_ip, e)

    def _reclaim_vip(self, vip: str, *, rebalance: bool = True) -> None:
        reclaim_ts = time()
        real_ip = self.V2R_Mappings.pop(vip, None)
        if not real_ip:
            return
        pool = self.host_vip_pools.get(real_ip)
        if pool:
            pool.discard(vip)
        # Check if this is a primary VIP being reclaimed
        is_primary = (self.host_primary_vip.get(real_ip) == vip)
        if is_primary:
            self.host_primary_vip.pop(real_ip, None)
            self.host_primary_assigned_at.pop(real_ip, None)
            self.host_primary_active_since.pop(real_ip, None)
            self.host_primary_ever_active.pop(real_ip, None)
        self.vip_created_at.pop(vip, None)
        self.vip_last_seen.pop(vip, None)
        self.vip_last_activity.pop(vip, None)
        self.vip_mac_map.pop(vip, None)
        self.vip_active_sessions.pop(vip, None)
        for k, v in list(self._reply_vip_by_5tuple.items()):
            if v == vip:
                self._reply_vip_by_5tuple.pop(k, None)
        for k, v in list(self.reply_vip_pair.items()):
            if v == vip:
                self.reply_vip_pair.pop(k, None)
        for key, value in list(self.session_last_contacted_vip.items()):
            if value == vip:
                self.session_last_contacted_vip.pop(key, None)
        for session_key, session in list(self.session_table.items()):
            if session.vip_dst == vip or session.vip_src == vip or session.vip_locked == vip:
                self._finalize_session(session_key, reclaim_ts, reason="vip reclaim")
        for key, value in list(self.icmp_echo_map.items()):
            if value[0] == vip:
                self.icmp_echo_map.pop(key, None)
        # Purge flows BEFORE putting VIP back in Resources
        # This ensures flows are fully deleted before VIP can be reused
        self._purge_flows_for_vip(vip)
        if vip not in self.Resources:
            # If this was a primary VIP, put it at the END to avoid immediate reassignment
            # For non-primary VIPs, put at front (normal behavior)
            if is_primary:
                self.Resources.append(vip)
            else:
                self.Resources.insert(0, vip)
        self.logger.info("RECLAIM: VIP %s reclaimed from %s", vip, real_ip)
        if rebalance and real_ip in self.detected_hosts:
            self._evaluate_host_state(real_ip, reclaim_ts)

    # ---------------- discovery ----------------
    def _learn_host(self, pkt, dpid):
        eth_pkt = pkt.get_protocol(ethernet.ethernet)
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        real_ip, mac = None, None
        if arp_pkt:
            real_ip, mac = arp_pkt.src_ip, arp_pkt.src_mac
        elif ip_pkt:
            real_ip, mac = ip_pkt.src, (eth_pkt.src if eth_pkt else None)
        else:
            return

        if real_ip in self.V2R_Mappings:
            return

        try:
            if not real_ip.startswith("10.0.0."):
                return
            last = int(real_ip.split(".")[-1])
            if last < 1 or last > self.DISCOVERY_RANGE_LAST_OCTET_MAX:
                return
        except Exception:
            return

        if real_ip in self.detected_hosts:
            if mac:
                self.host_ip_to_mac[real_ip] = mac
                self.host_mac_to_ip[mac] = real_ip
                self.HostAttachments[real_ip] = dpid
            return

        self.detected_hosts.add(real_ip)
        if mac:
            self.host_ip_to_mac[real_ip] = mac
            self.host_mac_to_ip[mac] = real_ip
            self.HostAttachments[real_ip] = dpid

        self.host_vip_pools.setdefault(real_ip, set())
        assigned: List[str] = []
        now = time()
        if self.INITIAL_ASSIGN_ON_DISCOVERY:
            primary = self._ensure_primary_vip(real_ip, now, force=True)
            if primary:
                assigned = [primary]
        self.logger.info("[+] New host %s (%s) - assigned %d VIPs: %s",
                         real_ip, mac, len(assigned), sorted(self.host_vip_pools[real_ip]))

    def _send_arp_reply(self, dp, ethertype, dst_mac, src_mac, src_ip, target_mac, target_ip, out_port):
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        p = packet.Packet()
        p.add_protocol(ethernet.ethernet(ethertype=ethertype, dst=dst_mac, src=src_mac))
        p.add_protocol(arp.arp(opcode=arp.ARP_REPLY,
                               src_mac=src_mac, src_ip=src_ip,
                               dst_mac=target_mac, dst_ip=target_ip))
        p.serialize()
        dp.send_msg(parser.OFPPacketOut(
            datapath=dp,
            buffer_id=ofp.OFP_NO_BUFFER,
            in_port=ofp.OFPP_CONTROLLER,
            actions=[parser.OFPActionOutput(out_port)],
            data=p.data))

    def _proactive_discovery(self, now: float) -> None:
        if not self.datapaths:
            return
        if not hasattr(self, "_last_discovery"):
            self._last_discovery = {}
        for last in range(1, self.DISCOVERY_RANGE_LAST_OCTET_MAX + 1):
            ip = f"10.0.0.{last}"
            if ip in self.V2R_Mappings:
                continue
            if ip in self._last_discovery and now - self._last_discovery[ip] < 60:
                continue
            self._last_discovery[ip] = now
            for dp in list(self.datapaths):
                try:
                    parser = dp.ofproto_parser
                    ofp = dp.ofproto
                    p = packet.Packet()
                    p.add_protocol(ethernet.ethernet(ethertype=0x0806,
                                                     dst='ff:ff:ff:ff:ff:ff', src='00:00:00:00:00:00'))
                    p.add_protocol(arp.arp(opcode=arp.ARP_REQUEST,
                                           src_mac='00:00:00:00:00:00', src_ip='10.0.0.254',
                                           dst_mac='00:00:00:00:00:00', dst_ip=ip))
                    p.serialize()
                    dp.send_msg(parser.OFPPacketOut(
                        datapath=dp,
                        buffer_id=ofp.OFP_NO_BUFFER,
                        in_port=ofp.OFPP_CONTROLLER,
                        actions=[parser.OFPActionOutput(ofp.OFPP_FLOOD)],
                        data=p.data))
                except Exception as e:
                    self.logger.debug("Discovery ARP to %s failed: %s", ip, e)

    # ---------------- selection helpers ----------------
    def _select_reply_vip_5tuple(self, server_real, client_real, proto, client_port, server_port):
        key = self._compose_reply_key(server_real, client_real, proto,
                                      client_port, server_port)
        vip = self._reply_vip_by_5tuple.get(key)
        if vip and self.V2R_Mappings.get(vip) == server_real:
            return vip
        return None

    # ---------------- logging ----------------
    def _log_vip_pools(self, now: float) -> None:
        self.logger.info("=== VIP POOLS ===")
        self.logger.info("DEBUG - V2R Mappings: %s", self.V2R_Mappings)
        self.logger.info("DEBUG - VIP last_seen: %s", self.vip_last_seen)

        def ipkey(ip):
            try:
                return tuple(int(x) for x in ip.split('.'))
            except Exception:
                return (ip,)

        total = 0
        active_total = 0
        for real_ip in sorted(self.detected_hosts, key=ipkey):
            pool = self.host_vip_pools.get(real_ip, set())
            primary = self.host_primary_vip.get(real_ip)
            if not pool:
                self.logger.info("Host %s: No VIPs assigned", real_ip)
                continue
            self.logger.info("Host %s (%d VIPs, primary=%s):", real_ip, len(pool), primary)
            self.logger.info(" %-13s %-9s %-8s %-10s %-12s", "VIP", "Uptime", "State", "Idle", "Primary")
            self.logger.info(" %-13s %-9s %-8s %-10s %-12s", "-------------", "---------", "--------", "----------", "----------")
            host_active = 0
            for vip in sorted(pool, key=ipkey):
                created = self.vip_created_at.get(vip, now)
                uptime = f"{max(0.0, (now - created)):.1f}s"
                last = self.vip_last_seen.get(vip)
                is_primary = "PRIMARY" if vip == primary else ""
                if self.vip_active_sessions.get(vip):
                    state = "ACTIVE"
                    idle_str = "-"
                    host_active += 1
                    active_total += 1
                else:
                    state = "IDLE"
                    if last is not None:
                        idle_str = f"{max(0.0, now - last):.1f}s"
                    else:
                        idle_str = "-"
                self.logger.info(" %-13s %-9s %-8s %-10s %-12s", vip, uptime, state, idle_str, is_primary)
                total += 1
            self.logger.info(" → %d active, %d idle", host_active, len(pool) - host_active)
        self.logger.info("=== SUMMARY: %d total VIPs (%d active, %d idle) ===",
                         total, active_total, total - active_total)

