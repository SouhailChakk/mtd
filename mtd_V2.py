"""
Moving Target Defense Ryu controller with dynamic VIP rotation and reply locking.
Rewritten from scratch to preserve legacy logging semantics while adding
per-packet randomized outbound VIP selection, reply VIP locking, and
comprehensive housekeeping.
"""

from dataclasses import dataclass, field
from time import time
from typing import Dict, List, Optional, Set, Tuple
from collections import defaultdict

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
    SESSION_NO_GROWTH_TIMEOUT = 10   # session "quiet" threshold (s)
    HOUSEKEEPING_INTERVAL = 15        # periodic tick (s)
    DISCOVERY_RANGE_LAST_OCTET_MAX = 10   # discover 10.0.0.1..10.0.0.10
    VIP_POOL_START = "10.0.0.11"         # first VIP (avoid clashing with discovered hosts)
    VIP_COOLING_PERIOD = 60          # seconds before reclaimed VIP can be reassigned
    VIP_REUSE_COOLDOWN = 5           # avoid re-using a VIP immediately after release (for SNAT)
    ROTATE_INTERVAL = 60             # Primary VIP rotation interval (seconds)
    GRACE_PERIOD = 5                 # seconds VIP stays in GRACE after rotation

    VIP_STATE_PRIMARY = "PRIMARY"
    VIP_STATE_GRACE = "GRACE"
    VIP_STATE_RECLAIMED = "RECLAIMED"
    
    # Cookie-based flow tracking
    COOKIE_BASE = 0xA000_0000_0000_0000
    COOKIE_VIP_MASK = 0xFFFF_FFFF
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
        # host_mac_to_ip can be derived from host_ip_to_mac, but kept for reverse lookup speed
        self.host_mac_to_ip: Dict[str, str] = {}

        # VIP state - consolidated to reduce redundancy
        self.V2R_Mappings: Dict[str, str] = {}  # VIP -> real_ip (also serves as vip_owner)
        self.host_vip_pools: Dict[str, Set[str]] = defaultdict(set)
        self.vip_mac_map: Dict[str, str] = {}
        self.vip_created_at: Dict[str, float] = {}  # Also used as vip_birth
        self.vip_last_seen: Dict[str, float] = {}  # Primary timestamp (vip_last_activity merged)
        # Removed: vip_idle_since - not needed for immediate reclaim based on session count
        self.vip_ever_active: Dict[str, float] = {}  # First activation time
        self.vip_reclaimed_at: Dict[str, float] = {}
        self.vip_recently_used: Dict[str, float] = {}
        
        # VIP rotation tracking - session count per VIP (refcount)
        self.vip_sessions: Dict[str, int] = defaultdict(int)  # active session count per VIP
        self.primary_vip: Dict[str, str] = {}  # exactly 1 primary VIP per host
        self.lingering_vips: Dict[str, Set[str]] = defaultdict(set)  # old primaries kept while active
        self.vip_state: Dict[str, str] = {}
        self.vip_grace_since: Dict[str, float] = {}
        self.last_rotate_ts: float = time()

        # reply VIP binding (legacy logging expectations)
        self.reply_vip_pair: Dict[Tuple[str, str, int], str] = {}
        self._reply_vip_by_5tuple: Dict[Tuple[str, str, int, int, int], str] = {}
        self.session_last_contacted_vip: Dict[Tuple[str, str, int, int, int], str] = {}

        # ICMP echo tracking so replies map back to the VIP that was contacted
        # even when multiple outstanding requests target different VIPs.
        self.icmp_echo_map: Dict[Tuple[str, str, int], Tuple[str, float]] = {}

        # Active session tracking per real host to support dynamic VIP scaling.
        self.host_active_sessions: Dict[str, Set[SessionKey]] = defaultdict(set)

        # VIP resource pool
        self.Resources: List[str] = self._generate_vips(self.VIP_POOL_START, self.NUM_VIPS)

        # sessions: session_table[key] -> SessionRecord
        self.session_table: Dict[SessionKey, SessionRecord] = {}

    # ---------------- lifecycle ----------------
    def start(self):
        super(MovingTargetDefense, self).start()
        self.threads.append(hub.spawn(self._ticker))
        self.threads.append(hub.spawn(self._rotation_loop))

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
        if vip not in self.vip_ever_active:
            self.vip_ever_active[vip] = ts
        if reason:
            self.logger.info("VIP TOUCH: %s last_seen=%.3f (%s)", vip, ts, reason)

    def _set_vip_state(self, vip: str, state: str, ts: float, reason: str = "") -> None:
        old_state = self.vip_state.get(vip)
        self.vip_state[vip] = state
        if state == self.VIP_STATE_GRACE:
            self.vip_grace_since[vip] = ts
        elif state in (self.VIP_STATE_PRIMARY, self.VIP_STATE_RECLAIMED):
            self.vip_grace_since.pop(vip, None)
        self.logger.info("VIP STATE: %s %s -> %s (%s)", vip, old_state or "<new>", state, reason or "no-reason")

    def _mark_vip_reuse(self, vip: str, ts: float) -> None:
        if vip:
            self.vip_recently_used[vip] = ts

    def _on_session_start(self, vip: str) -> None:
        """Called when a new session is established to destination VIP."""
        if vip:
            self.vip_sessions[vip] += 1
    
    def _on_session_end(self, vip: str) -> None:
        """Called when a session to destination VIP ends."""
        if not vip:
            return
        if self.vip_sessions[vip] > 0:
            self.vip_sessions[vip] -= 1
        self._maybe_reclaim_vip(vip, time(), reason="session end")

    def _maybe_reclaim_vip(self, vip: str, now: float, reason: str = "") -> bool:
        """Reclaim VIP only if it is non-primary, idle, and beyond grace by last-seen."""
        owner = self.V2R_Mappings.get(vip)
        if not owner:
            return False
        if self.primary_vip.get(owner) == vip:
            self.logger.info("RECLAIM CHECK: %s skip (PRIMARY)", vip)
            return False

        sessions = self.vip_sessions.get(vip, 0)
        last_seen = self.vip_last_seen.get(vip, now)
        age = now - last_seen
        grace_since = self.vip_grace_since.get(vip, now)
        grace_age = now - grace_since

        if sessions == 0 and age > self.GRACE_PERIOD and grace_age > self.GRACE_PERIOD:
            self.logger.info("RECLAIM CHECK: %s reclaim (sessions=%d, last_seen_age=%.2fs, grace_age=%.2fs, reason=%s)",
                             vip, sessions, age, grace_age, reason or "n/a")
            self._reclaim_vip(vip)
            return True

        self.logger.info("RECLAIM CHECK: %s defer (sessions=%d, last_seen_age=%.2fs, grace_age=%.2fs, reason=%s)",
                         vip, sessions, age, grace_age, reason or "n/a")
        return False

    def _check_active_sessions(self, vip: str) -> bool:
        """Return True if any active session still references this VIP."""
        if self.vip_sessions.get(vip, 0) > 0:
            return True
        for session in self.session_table.values():
            if vip in (session.vip_dst, session.vip_src, session.vip_locked, session.last_reply_vip):
                return True
        return False

    def _ensure_primary_vip(self, real_ip: str, now: float) -> Optional[str]:
        """Ensure a host has exactly one primary VIP and return it."""
        current = self.primary_vip.get(real_ip)
        if current and self.V2R_Mappings.get(current) == real_ip:
            return current
        vip = self._take_resource_vip(now)
        if not vip:
            self.logger.error("VIP: unable to assign primary for %s (pool exhausted)", real_ip)
            return None
        self._bind_vip_to_host(vip, real_ip, now)
        self.primary_vip[real_ip] = vip
        self.lingering_vips[real_ip] = set()
        self._set_vip_state(vip, self.VIP_STATE_PRIMARY, now, reason="ensure primary")
        self._send_gratuitous_arp_to_all(vip)
        self._send_targeted_arp_updates(vip)
        self.logger.info("VIP: assigned primary %s -> %s", real_ip, vip)
        return vip

    def _extract_icmp_echo_fields(self, icmp_pkt) -> Tuple[Optional[int], Optional[int]]:
        """Extract ICMP echo id/seq robustly across payload shapes."""
        if not icmp_pkt or not hasattr(icmp_pkt, "data"):
            return None, None
        echo_id = getattr(icmp_pkt.data, "id", None)
        echo_seq = getattr(icmp_pkt.data, "seq", None)

        if echo_id is None:
            return None, None

        try:
            echo_id = int(echo_id)
        except Exception:
            return None, None

        # Some packet decoders expose packed id|seq in one field.
        # When detected, always treat high-16 bits as echo-id (stable across
        # a ping stream) and low-16 bits as sequence.
        if echo_id > 0xFFFF:
            packed = echo_id
            packed_hi = (packed >> 16) & 0xFFFF
            packed_lo = packed & 0xFFFF
            seq_i = None
            if echo_seq is not None:
                try:
                    seq_i = int(echo_seq) & 0xFFFF
                except Exception:
                    seq_i = None
            return packed_hi, (seq_i if seq_i is not None else packed_lo)

        try:
            echo_seq_i = int(echo_seq) & 0xFFFF if echo_seq is not None else None
        except Exception:
            echo_seq_i = None

        return echo_id & 0xFFFF, echo_seq_i

    # Removed: _flag_vip_idle and _start_idle_timer
    # Primary VIP rotation uses immediate reclaim based on session count, not idle timers

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

        # 2) evaluate reclaim for GRACE VIPs
        for host_ip, grace_vips in list(self.lingering_vips.items()):
            for vip in list(grace_vips):
                if self._maybe_reclaim_vip(vip, now, reason="housekeeping"):
                    grace_vips.discard(vip)
            if not grace_vips:
                self.lingering_vips.pop(host_ip, None)

        # 5) proactive (light) discovery
        self._proactive_discovery(now)

        # 6) prune stale ICMP echo bindings so the map does not grow without bound
        icmp_expiry = self.SESSION_NO_GROWTH_TIMEOUT * 4
        for key, (vip, ts) in list(self.icmp_echo_map.items()):
            if (now - ts) > icmp_expiry:
                self.icmp_echo_map.pop(key, None)

        # 7) log cooling period status
        cooling_vips = [vip for vip, ts in self.vip_reclaimed_at.items()
                        if (now - ts) < self.VIP_COOLING_PERIOD]
        if cooling_vips:
            self.logger.info("COOLING: %d VIPs in cooling period: %s",
                             len(cooling_vips), sorted(cooling_vips)[:5])

        # 8) log snapshot
        self._log_vip_pools(now)

    # Removed: _desired_vip_target, _top_up_host, _trim_host_vips, _rebalance_host_vips
    # These were for dynamic VIP scaling, not needed for primary VIP rotation

    def _take_resource_vip(self, now: float) -> Optional[str]:
        for idx, candidate in enumerate(self.Resources):
            if candidate in self.vip_reclaimed_at:
                if (now - self.vip_reclaimed_at[candidate]) < self.VIP_COOLING_PERIOD:
                    continue
            return self.Resources.pop(idx)
        return None

    def _bind_vip_to_host(self, vip: str, real_ip: str, now: float) -> None:
        """Bind VIP to host and initialize state."""
        self.vip_reclaimed_at.pop(vip, None)
        self.V2R_Mappings[vip] = real_ip
        self.host_vip_pools[real_ip].add(vip)
        self.vip_created_at[vip] = now
        self.vip_last_seen[vip] = now
        self.vip_ever_active.pop(vip, None)
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
        self.vip_sessions[vip] = 0  # Session count starts at 0
        self._set_vip_state(vip, self.VIP_STATE_PRIMARY, now, reason="bind host")
        self._purge_flows_for_vip(vip)
    
    def _ip_to_int(self, ip: str) -> int:
        """Convert IP address string to integer."""
        parts = ip.split('.')
        return (int(parts[0]) << 24) + (int(parts[1]) << 16) + (int(parts[2]) << 8) + int(parts[3])
    
    def _int_to_ip(self, val: int) -> str:
        """Convert integer to IP address string."""
        return f"{(val >> 24) & 0xFF}.{(val >> 16) & 0xFF}.{(val >> 8) & 0xFF}.{val & 0xFF}"
    
    def _delete_flows_by_cookie(self, datapath, cookie: int) -> None:
        """Delete all flows matching the given cookie."""
        parser = datapath.ofproto_parser
        ofproto = datapath.ofproto
        match = parser.OFPMatch()
        # Use full 64-bit mask to match exact cookie (COOKIE_BASE + VIP)
        cookie_mask = 0xFFFF_FFFF_FFFF_FFFF
        mod = parser.OFPFlowMod(
            datapath=datapath,
            table_id=ofproto.OFPTT_ALL,
            command=ofproto.OFPFC_DELETE,
            out_port=ofproto.OFPP_ANY,
            out_group=ofproto.OFPG_ANY,
            match=match,
            cookie=cookie,
            cookie_mask=cookie_mask,
        )
        datapath.send_msg(mod)
    
    def _rotation_loop(self) -> None:
        """Periodically rotate primary VIPs for each host (every 60s)."""
        while True:
            hub.sleep(self.ROTATE_INTERVAL)
            self.last_rotate_ts = time()
            now = time()
            
            for host_ip in sorted(self.detected_hosts):
                old_vip = self.primary_vip.get(host_ip)
                
                # 1) Always assign new primary VIP (every 60s)
                new_vip = self._take_resource_vip(now)
                if not new_vip:
                    self.logger.warning("ROTATE: No VIP available for %s", host_ip)
                    continue
                
                self._bind_vip_to_host(new_vip, host_ip, now)
                self.primary_vip[host_ip] = new_vip
                
                # Announce new primary VIP to network
                self._send_gratuitous_arp_to_all(new_vip)
                self._send_targeted_arp_updates(new_vip)
                
                # 2) Move old primary into GRACE state.
                if old_vip and old_vip != new_vip:
                    self.lingering_vips[host_ip].add(old_vip)
                    self._set_vip_state(old_vip, self.VIP_STATE_GRACE, now, reason=f"rotation {host_ip}")
                    self.logger.info("ROTATE: %s -> %s (old %s moved to GRACE)", host_ip, new_vip, old_vip)
                    # Keep flows installed for GRACE VIP; reclaim is deferred.
                    self._maybe_reclaim_vip(old_vip, now, reason="rotation checkpoint")

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

        # ---- ARP ----
        a = pkt.get_protocol(arp.arp)
        if a and a.opcode == arp.ARP_REQUEST:
            dip, sip, smac = a.dst_ip, a.src_ip, a.src_mac

            # For primary VIP rotation: don't lazy-assign VIPs
            # VIPs are only assigned by rotation loop or on host discovery
            # Lazy assignment disabled to maintain exactly one primary VIP per host

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

        # ---- IPv4 ----
        ip4 = pkt.get_protocol(ipv4.ipv4)
        if not ip4:
            return

        tcp_pkt = pkt.get_protocol(tcp.tcp)
        udp_pkt = pkt.get_protocol(udp.udp)
        icmp_pkt = pkt.get_protocol(icmp.icmp)

        src_ip, dst_ip, proto = ip4.src, ip4.dst, ip4.proto
        src_port = tcp_pkt.src_port if tcp_pkt else (udp_pkt.src_port if udp_pkt else 0)
        dst_port = tcp_pkt.dst_port if tcp_pkt else (udp_pkt.dst_port if udp_pkt else 0)
        if proto == 1:
            echo_id, _echo_seq = self._extract_icmp_echo_fields(icmp_pkt)
            if echo_id is not None:
                # Keep ICMP session continuity across rotation by keying the
                # session on echo-id (stable for a ping process), not seq.
                icmp_token = int(echo_id) & 0xFFFF
                src_port = icmp_token
                dst_port = icmp_token
            else:
                # Fallback for uncommon ICMP payload shapes: keep a stable key
                # so one ongoing flow does not get remapped on rotation.
                src_port = 0
                dst_port = 0
        now = time()
        # self.logger.info("PACKET: %s -> %s (proto %d)", src_ip, dst_ip, proto)

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
                host_sessions = self.host_active_sessions[host]
                host_sessions.add(session_key)
                affected_hosts.add(host)
            # Primary VIP rotation handles VIP assignment, no dynamic scaling on session creation
            # for host in affected_hosts:
            #     self._rebalance_host_vips(host, now)

        vip_dst = None
        forward_dst_mac = None

        # CRITICAL: For existing sessions, ALWAYS use the VIP the session started with
        # This ensures session continuity even after VIP rotation
        if session and session.vip_dst:
            # Existing session: use the VIP it started with (may be lingering)
            vip_dst = session.vip_dst
            if vip_dst in self.V2R_Mappings:
                real_dst = self.V2R_Mappings[vip_dst]
            else:
                # VIP was reclaimed but session still exists - this shouldn't happen
                # but fallback to primary VIP
                if server_real in self.primary_vip:
                    vip_dst = self.primary_vip[server_real]
                    real_dst = server_real
                else:
                    real_dst = server_real
        # For new sessions, use primary VIP for the destination host
        elif direction == 'forward' and new_session:
            # New session: MUST use current primary VIP for destination host.
            if server_real in self.detected_hosts:
                vip_dst = self._ensure_primary_vip(server_real, now)
                if vip_dst:
                    real_dst = server_real
                    self._on_session_start(vip_dst)
                else:
                    # Allocation failure: keep routing to real destination, keep old primary if any.
                    real_dst = server_real
            else:
                # External destination or unknown
                real_dst = dst_ip
        elif dst_ip in self.V2R_Mappings:
            # Packet to a VIP (but session doesn't have vip_dst set yet)
            # Only set vip_dst if session doesn't already have one
            if not session.vip_dst:
                vip_dst = dst_ip
                real_dst = self.V2R_Mappings[dst_ip]
                if new_session:
                    self._on_session_start(vip_dst)
            else:
                # Session already has vip_dst, use it
                vip_dst = session.vip_dst
                real_dst = self.V2R_Mappings.get(vip_dst, server_real)
        elif server_real in self.primary_vip:
            # Destination host has primary VIP, use it (for new sessions only)
            # Only if session doesn't already have a vip_dst
            if not session.vip_dst:
                vip_dst = self.primary_vip[server_real]
                real_dst = server_real
                if new_session:
                    self._on_session_start(vip_dst)
            else:
                # Session already has vip_dst, use it
                vip_dst = session.vip_dst
                real_dst = self.V2R_Mappings.get(vip_dst, server_real)
        else:
            # External destination
            real_dst = dst_ip
        
        if vip_dst:
            actions.append(parser.OFPActionSetField(ipv4_dst=real_dst))
            dst_mac = self.host_ip_to_mac.get(real_dst)
            if dst_mac:
                actions.append(parser.OFPActionSetField(eth_dst=dst_mac))
                forward_dst_mac = dst_mac
            # CRITICAL: Only set session.vip_dst if it's not already set
            # This preserves the original VIP the session started with
            if not session.vip_dst:
                session.vip_dst = vip_dst
            session.last_contacted_vip = vip_dst
            # If replies were previously using a different VIP, detach it so a
            # reclaimed VIP cannot linger as the preferred reverse mapping.
            if session.last_reply_vip and session.last_reply_vip != vip_dst:
                self._mark_vip_reuse(session.last_reply_vip, now)
                session.last_reply_vip = None
            if proto != 1 and not session.vip_locked:
                session.vip_locked = vip_dst
            self._touch_vip(vip_dst, now, "session create: vip_dst")
            self._register_reply_mapping(session, server_real, client_real,
                                         proto, vip_dst, client_port, server_port,
                                         icmp_pkt, tcp_pkt, udp_pkt)
            if icmp_pkt and getattr(icmp_pkt, "type", None) == 8:
                echo_id, _echo_seq = self._extract_icmp_echo_fields(icmp_pkt)
                if echo_id is not None:
                    key = (server_real, client_real, int(echo_id))
                    self.icmp_echo_map[key] = (vip_dst, now)
            if direction == 'forward' and vip_dst:
                flow_key = (client_real, server_real, proto, client_port, server_port)
                self.session_last_contacted_vip[flow_key] = vip_dst

        if direction == 'forward':
            binding_vip = None
            if vip_dst:
                bound = session.vip_src_by_target.get(vip_dst)
                if bound and self.V2R_Mappings.get(bound) == client_real:
                    binding_vip = bound
                elif bound:
                    session.vip_src_by_target.pop(vip_dst, None)

            vip_src = session.vip_src
            need_new_vip = False
            
            previous_target = session.active_target_vip
            freed_previous = False
            previous_vip_src = None

            if binding_vip and vip_src and vip_src != binding_vip:
                previous_vip_src = vip_src
                previous_target = session.active_target_vip
                self._mark_vip_reuse(previous_vip_src, now)
                session.vip_src = None
                vip_src = None
                session.active_target_vip = None
                if previous_target:
                    session.vip_src_by_target.pop(previous_target, None)
                previous_vip_src = None
                previous_target = None

            if binding_vip and not vip_src:
                vip_src = binding_vip
                session.vip_src = vip_src
                session.active_target_vip = vip_dst
                session.vip_src_by_target[vip_dst] = vip_src
                session.last_vip_src_use = now
                session.last_vip_src_announce = 0.0
                self._touch_vip(vip_src, now, "reuse target binding")
                self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
                session.last_vip_src_announce = now

            if vip_src:
                owner = self.V2R_Mappings.get(vip_src)
                if owner != client_real:
                    previous_vip_src = vip_src
                    previous_target = session.active_target_vip
                    need_new_vip = True
                else:
                    elapsed = now - session.last_vip_src_use if session.last_vip_src_use else 0.0
                    if elapsed > self.SESSION_NO_GROWTH_TIMEOUT:
                        previous_vip_src = vip_src
                        previous_target = session.active_target_vip
                        need_new_vip = True
                    else:
                        if vip_dst:
                            if session.vip_src_by_target.get(vip_dst) != vip_src:
                                session.vip_src_by_target[vip_dst] = vip_src
                        session.active_target_vip = vip_dst
                        if (now - session.last_vip_src_announce) >= self.SESSION_NO_GROWTH_TIMEOUT:
                            self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
                            session.last_vip_src_announce = now
                        session.last_vip_src_use = now
            else:
                need_new_vip = True

            if need_new_vip and previous_vip_src:
                self._mark_vip_reuse(previous_vip_src, now)
                if previous_target:
                    session.vip_src_by_target.pop(previous_target, None)
                session.vip_src = None
                session.active_target_vip = None
                vip_src = None

            if need_new_vip:
                # For primary VIP rotation: use primary VIP or existing VIPs in pool
                # Don't allocate new VIPs dynamically - only rotation loop assigns VIPs
                vip_src = self._choose_outbound_vip(client_real, now)
                if not vip_src:
                    # Fallback: use primary VIP if available
                    if client_real in self.primary_vip:
                        vip_src = self.primary_vip[client_real]
                if not vip_src and previous_vip_src and self.V2R_Mappings.get(previous_vip_src) == client_real:
                    vip_src = previous_vip_src

                if not vip_src:
                    session.vip_src = None
                else:
                    session.vip_src = vip_src
                    session.active_target_vip = vip_dst
                    if vip_dst:
                        session.vip_src_by_target[vip_dst] = vip_src
                    session.last_vip_src_use = now
                    session.last_vip_src_announce = 0.0
                    self._touch_vip(vip_src, now, "session create: vip_src")
                    self._mark_vip_reuse(vip_src, now)
                    self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
                    session.last_vip_src_announce = now

            if not session.vip_src:
                vip_src = self.primary_vip.get(client_real)
                if vip_src and self.V2R_Mappings.get(vip_src) == client_real:
                    session.vip_src = vip_src
                    session.active_target_vip = vip_dst
                    if vip_dst:
                        session.vip_src_by_target[vip_dst] = vip_src
                    session.last_vip_src_use = now
                    self._touch_vip(vip_src, now, "fallback vip_src assign")
                    self._mark_vip_reuse(vip_src, now)
                    # ensure peer learns the VIP MAC before packets flow
                    self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
                    session.last_vip_src_announce = now

            if session.vip_src:
                mac = self.vip_mac_map.get(session.vip_src) or self._generate_vip_mac(session.vip_src)
                self.vip_mac_map[session.vip_src] = mac
                actions.append(parser.OFPActionSetField(ipv4_src=session.vip_src))
                actions.append(parser.OFPActionSetField(eth_src=mac))
            if not forward_dst_mac:
                forward_dst_mac = self.host_ip_to_mac.get(server_real)
        else:  # reverse direction (server -> client)
            # CRITICAL: For primary VIP rotation, replies MUST use the same VIP the session started with
            # This ensures active sessions continue using their original VIP even after rotation
            vip_src = None
            
            # Priority 1: Use the VIP the session started with (session.vip_dst)
            # This is the most important - it ensures continuity after rotation
            if session.vip_dst and self.V2R_Mappings.get(session.vip_dst) == server_real:
                vip_src = session.vip_dst
            # Priority 2: Use locked VIP if set (for non-ICMP)
            elif session.vip_locked and self.V2R_Mappings.get(session.vip_locked) == server_real:
                vip_src = session.vip_locked
            # Priority 3: Use last reply VIP (for consistency)
            elif session.last_reply_vip and self.V2R_Mappings.get(session.last_reply_vip) == server_real:
                vip_src = session.last_reply_vip
            # Priority 4: For ICMP, check echo map
            elif proto == 1 and icmp_pkt and getattr(icmp_pkt, "type", None) == 0:
                echo_id, _echo_seq = self._extract_icmp_echo_fields(icmp_pkt)
                if echo_id is not None:
                    key = (server_real, client_real, int(echo_id))
                    stored = self.icmp_echo_map.get(key)
                    if stored:
                        candidate_vip, _stored_ts = stored
                        if self.V2R_Mappings.get(candidate_vip) == server_real:
                            vip_src = candidate_vip
            # Priority 5: Fallback to any lingering VIP for this host
            if not vip_src:
                # Check lingering VIPs first (these are old primaries with active sessions)
                lingering = self.lingering_vips.get(server_real, set())
                for candidate in lingering:
                    if self.V2R_Mappings.get(candidate) == server_real:
                        vip_src = candidate
                        break
                # Last resort: use primary VIP (but this should rarely happen for existing sessions)
                if not vip_src and server_real in self.primary_vip:
                    vip_src = self.primary_vip[server_real]

            if vip_src:
                previous_reply_vip = session.last_reply_vip
                freed_prev = False
                if previous_reply_vip and previous_reply_vip != vip_src:
                    self._mark_vip_reuse(previous_reply_vip, now)
                if proto != 1:
                    session.vip_locked = vip_src
                self._touch_vip(vip_src, now, "reply packet")
                mac = self.vip_mac_map.get(vip_src) or self._generate_vip_mac(vip_src)
                self.vip_mac_map[vip_src] = mac
                actions.append(parser.OFPActionSetField(ipv4_src=vip_src))
                actions.append(parser.OFPActionSetField(eth_src=mac))
                session.last_reply_vip = vip_src
                self._mark_vip_reuse(vip_src, now)
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
            elif dst_ip in self.V2R_Mappings:
                # Check if it's a lingering VIP (V2R_Mappings also serves as vip_owner)
                owner = self.V2R_Mappings.get(dst_ip)
                if owner and dst_ip in self.lingering_vips[owner]:
                    real_dst = owner
                else:
                    real_dst = dst_ip
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
            self.logger.info("SESSION: created %s -> %s (proto %d) vip_dst=%s (session_key=%s)",
                             src_ip, dst_ip, proto, session.vip_dst, session.key)

        session.packet_count += 1
        session.last_growth = now
        if session.vip_src:
            self._touch_vip(session.vip_src, now, "packet activity: vip_src")
        if session.vip_locked:
            self._touch_vip(session.vip_locked, now, "packet activity: vip_locked")
        elif session.vip_dst:
            self._touch_vip(session.vip_dst, now, "packet activity: vip_dst")
        # self.logger.info("DEBUG: Session found/created for %s->%s, vip_dst=%s",
        #                  src_ip, dst_ip, session.vip_dst)

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
            host_sessions = self.host_active_sessions[host]
            if session_key in host_sessions:
                host_sessions.discard(session_key)
                if not host_sessions:
                    del self.host_active_sessions[host]
                affected_hosts.add(host)
        # Primary VIP rotation handles VIP assignment, no dynamic scaling on session end
        # if reason != "vip reclaim":
        #     for host in affected_hosts:
        #         if host in self.detected_hosts:
        #             self._rebalance_host_vips(host, ts)

        for key in session.reply_keys:
            self._reply_vip_by_5tuple.pop(key, None)
        pair_key = (session.key[1], session.key[0], session.proto)
        if self.reply_vip_pair.get(pair_key) == session.vip_locked:
            self.reply_vip_pair.pop(pair_key, None)

        # Decrement refcount only for destination VIP tracked by session start.
        if session.vip_dst:
            self._on_session_end(session.vip_dst)
            self._mark_vip_reuse(session.vip_dst, ts)

        flow_key = (session.key[0], session.key[1], session.proto, session.key[3], session.key[4])
        reverse_key = (session.key[1], session.key[0], session.proto, session.key[4], session.key[3])
        self.session_last_contacted_vip.pop(flow_key, None)
        self.session_last_contacted_vip.pop(reverse_key, None)

        if session.proto == 1:
            for key in list(self.icmp_echo_map.keys()):
                if len(key) >= 2:
                    server_real, client_real = key[0], key[1]
                    if server_real == session.key[1] and client_real == session.key[0]:
                        self.icmp_echo_map.pop(key, None)

    def _choose_outbound_vip(self, real_ip: str, now: float) -> Optional[str]:
        # Keep source identity stable: prefer current primary VIP only.
        current_primary = self.primary_vip.get(real_ip)
        if current_primary and self.V2R_Mappings.get(current_primary) == real_ip:
            return current_primary

        # Fallback only if primary is missing/inconsistent.
        pool = self.host_vip_pools.get(real_ip)
        if not pool:
            return None
        for vip in pool:
            if self.V2R_Mappings.get(vip) == real_ip:
                return vip
        return None

    def _compose_reply_key(self, server_real: str, client_real: str,
                           proto: int, client_port: int, server_port: int) -> Tuple[str, str, int, int, int]:
        if proto == 1:
            return (server_real, client_real, 1, client_port, server_port)
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
        # self.logger.info("REPLY MAPPING: server=%s client=%s proto=%d uses VIP %s (5tuple key=%s)",
        #                  server_real, client_real, proto, vip_dst, key)

    # ---------------- VIP helpers ----------------
    # Removed: _allocate_vip_to_host
    # For primary VIP rotation, VIPs are only assigned by rotation loop, not on-demand
    # def _allocate_vip_to_host(self, real_ip: str, now: float, announce: bool = True) -> Optional[str]:
    #     # Disabled for primary VIP rotation
    #     return None

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

    def _reclaim_vip(self, vip: str) -> None:
        """Reclaim a VIP. CRITICAL: Only call this if VIP has NO active sessions."""
        reclaim_ts = time()
        
        # SAFETY CHECK: Verify VIP is not in active sessions before reclaiming.
        if self._check_active_sessions(vip):
            self.logger.warning("RECLAIM: Attempted to reclaim VIP %s with active sessions, aborting", vip)
            return
        self._set_vip_state(vip, self.VIP_STATE_RECLAIMED, reclaim_ts, reason="reclaim")
        
        real_ip = self.V2R_Mappings.pop(vip, None)
        if not real_ip:
            # Also check if it's a lingering VIP
            for host, lingering_set in self.lingering_vips.items():
                if vip in lingering_set:
                    real_ip = host
                    lingering_set.discard(vip)
                    if not lingering_set:
                        self.lingering_vips.pop(host, None)
                    break
        if not real_ip:
            return
        
        # Remove from primary if it was primary
        if self.primary_vip.get(real_ip) == vip:
            self.primary_vip.pop(real_ip, None)
        
        self.host_vip_pools[real_ip].discard(vip)
        self.vip_created_at.pop(vip, None)
        self.vip_last_seen.pop(vip, None)
        self.vip_ever_active.pop(vip, None)
        self.vip_mac_map.pop(vip, None)
        self.vip_recently_used.pop(vip, None)
        self.vip_sessions.pop(vip, None)
        self.vip_state.pop(vip, None)
        self.vip_grace_since.pop(vip, None)
        
        # Delete flows for this VIP
        vip_cookie = self.COOKIE_BASE | (self._ip_to_int(vip) & self.COOKIE_VIP_MASK)
        for datapath in list(self.datapaths):
            self._delete_flows_by_cookie(datapath, vip_cookie)
        
        for k, v in list(self._reply_vip_by_5tuple.items()):
            if v == vip:
                self._reply_vip_by_5tuple.pop(k, None)
        for k, v in list(self.reply_vip_pair.items()):
            if v == vip:
                self.reply_vip_pair.pop(k, None)
        for key, value in list(self.session_last_contacted_vip.items()):
            if value == vip:
                self.session_last_contacted_vip.pop(key, None)
        for session in self.session_table.values():
            if session.last_reply_vip == vip:
                session.last_reply_vip = None
            if session.vip_locked == vip:
                session.vip_locked = None
            if session.vip_src == vip:
                session.vip_src = None
        for key, value in list(self.icmp_echo_map.items()):
            if value[0] == vip:
                self.icmp_echo_map.pop(key, None)
        self._purge_flows_for_vip(vip)
        self.vip_reclaimed_at[vip] = reclaim_ts
        if vip not in self.Resources:
            self.Resources.insert(0, vip)
        self.logger.info("RECLAIM: VIP %s reclaimed from %s (cooling period started)", vip, real_ip)
        # Primary VIP rotation handles VIP assignment, no dynamic scaling on reclaim
        # if real_ip in self.detected_hosts:
        #     self._rebalance_host_vips(real_ip, reclaim_ts)

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

        # Initialize primary VIP on discovery
        if real_ip not in self.primary_vip:
            now = time()
            vip = self._ensure_primary_vip(real_ip, now)
            if vip:
                self.logger.info("[+] New host %s (%s) - assigned primary VIP: %s", real_ip, mac, vip)

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
            pool = self.host_vip_pools[real_ip]
            if not pool:
                self.logger.info("Host %s: No VIPs assigned", real_ip)
                continue
            self.logger.info("Host %s (%d VIPs):", real_ip, len(pool))
            self.logger.info(" %-13s %-9s %-8s %-10s %-12s", "VIP", "Uptime", "State", "Idle", "Reclaim")
            self.logger.info(" %-13s %-9s %-8s %-10s %-12s", "-------------", "---------", "--------", "----------", "----------")
            host_active = 0
            for vip in sorted(pool, key=ipkey):
                created = self.vip_created_at.get(vip, now)
                uptime = f"{max(0.0, (now - created)):.1f}s"
                last = self.vip_last_seen.get(vip)
                # State based on session count (primary VIP rotation logic)
                # Check if VIP is used by any active session (destination or source)
                is_active = self.vip_sessions[vip] > 0
                if not is_active:
                    # Also check if any session is using this VIP as destination or source
                    for session in self.session_table.values():
                        if session.vip_dst == vip or session.vip_src == vip or session.vip_locked == vip:
                            is_active = True
                            break
                
                vip_sm_state = self.vip_state.get(vip, "UNKNOWN")
                if is_active:
                    state = f"{vip_sm_state}*"
                    idle_str = "-"
                    recl_str = "-"
                    host_active += 1
                    active_total += 1
                else:
                    state = vip_sm_state
                    idle_str = "-"
                    recl_str = "-"
                self.logger.info(" %-13s %-9s %-8s %-10s %-12s", vip, uptime, state, idle_str, recl_str)
                total += 1
            self.logger.info(" → %d active, %d idle", host_active, len(pool) - host_active)
        self.logger.info("=== SUMMARY: %d total VIPs (%d active, %d idle) ===",
                         total, active_total, total - active_total)
    
    # ---------------- flow removal tracking ----------------
    @set_ev_cls(ofp_event.EventOFPFlowRemoved, MAIN_DISPATCHER)
    def _flow_removed_handler(self, ev) -> None:
        """Track flow removals - check if lingering VIPs can be reclaimed."""
        # Note: mtd_v3.py uses packet-out, not flow installation
        # We track VIP usage via vip_sessions (refcount) for rotation
        # This handler is here for future flow-based implementations
        pass
