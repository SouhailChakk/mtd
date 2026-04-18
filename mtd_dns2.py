import socket
from time import time
from typing import Dict, List, Optional, Set, Tuple
import ipaddress

from ryu.base import app_manager
from ryu.controller import event, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, set_ev_cls
from ryu.lib import hub
from ryu.lib.packet import arp, ethernet, icmp, ipv4, packet, tcp, udp
from ryu.ofproto import ofproto_v1_3
from ryu.topology import event as topo_event
from ryu.topology.api import get_link, get_switch


class EventMessage(event.EventBase):
    def __init__(self, message: str):
        super(EventMessage, self).__init__()


class MovingTargetDefenseDNS(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _EVENTS = [EventMessage]

    NUM_VIPS = 8000
    HOUSEKEEPING_INTERVAL = 15
    ROTATE_INTERVAL = 60
    TCP_SYN_SEEN_TIMEOUT = 15
    TCP_ESTABLISHED_TIMEOUT = 15
    TCP_CLOSING_TIMEOUT = 8
    UDP_ACTIVE_TIMEOUT = 30
    VIP_INACTIVITY_RECLAIM = 5
    VIP_QUARANTINE_SECONDS = 30
    # GRACE VIPs: If idle when moved to GRACE (flow_refs = 0), reclaim immediately (return to pool)
    #             If active when moved to GRACE (flow_refs > 0), keep until flows end
    REAL_HOST_SUBNET = "10.0.0.0/8"
    REAL_HOST_POOL_SIZE = (1 << (32 - 8)) - 2
    PROACTIVE_DISCOVERY_BATCH = 512
    VIP_POOL_START = "10.0.2.1"

    FLOW_PRIORITY_VIP = 100
    COOKIE_BASE = 0xA000_0000_0000_0000
    COOKIE_VIP_MASK = 0xFFFF_FFFF
    CONTROLLER_DISCOVERY_MAC = "02:00:00:00:00:fe"
    CONTROLLER_DISCOVERY_IP = "10.255.255.254"

    # Topology discovery: switches + links only (hosts excluded for fair benchmark)
    EXPECTED_SWITCHES = 28
    EXPECTED_DIRECTED_LINKS = 2
    EXPECTED_HOSTS = 0  # 0 = do not wait for host discovery

    VIP_STATE_PRIMARY = "PRIMARY"
    VIP_STATE_GRACE = "GRACE"
    SESSION_TCP_SYN_SEEN = "SYN_SEEN"
    SESSION_TCP_ESTABLISHED = "ESTABLISHED"
    SESSION_TCP_CLOSING = "CLOSING"
    SESSION_UDP_ACTIVE = "ACTIVE"

    def __init__(self, *args, **kwargs):
        super(MovingTargetDefenseDNS, self).__init__(*args, **kwargs)

        # Network topology tracking
        self.mac_to_port: Dict[int, Dict[str, int]] = {}  # dpid -> {mac: port}
        self.datapaths: Set["ryu.controller.controller.Datapath"] = set()
        
        # Host discovery and mapping
        self.detected_hosts: Set[str] = set()  # Set of discovered real host IPs in first REAL_HOST_POOL_SIZE addresses
        self.host_ip_to_mac: Dict[str, str] = {}  # Real host IP -> MAC address
        
        # VIP assignment and state
        self.primary_vip: Dict[str, str] = {}  # Real host IP -> Primary VIP assigned to that host
        self.vip_owner: Dict[str, str] = {}  # VIP -> Real host IP (reverse mapping)
        self.vip_state: Dict[str, str] = {}  # VIP -> State (PRIMARY, GRACE)
        self.vip_mac_map: Dict[str, str] = {}  # VIP -> Generated MAC address for that VIP
        self.vip_created_at: Dict[str, float] = {}  # VIP -> Timestamp when VIP was created/assigned
        self.host_vip_pools: Dict[str, Set[str]] = {}  # Real host IP -> Set of all VIPs assigned to that host
        
        # Activity tracking
        self.vip_flow_refs: Dict[str, int] = {}  # VIP -> Number of installed dataplane flows still alive
        self.vip_session_refs: Dict[str, int] = {}  # VIP -> Active controller-side sessions pinned to VIP
        self.vip_last_seen: Dict[str, float] = {}  # VIP -> Last observed session activity
        self.quarantine_until: Dict[str, float] = {}  # VIP -> Earliest timestamp eligible for reuse
        self.vip_delete_requested_at: Dict[str, float] = {}  # VIP -> Last cookie delete request time

        # L4 session handling for TCP/UDP NAT consistency
        self.session_table: Dict[Tuple[str, str, int, int, int], Dict[str, object]] = {}
        
        # VIP resource pool
        self.Resources: List[str] = self._generate_vips(self.VIP_POOL_START, self.NUM_VIPS)

        # Topology discovery timing (switches + links only)
        self.discovery_start_time = time()
        self.discovery_end_time: Optional[float] = None
        self.discovery_completed = False
        self.discovery_completion_reason = ""
        self.real_host_network = ipaddress.ip_network(self.REAL_HOST_SUBNET, strict=False)
        self._discovery_next_host_index = 1

    # ---------------- lifecycle ----------------

    def start(self):
        super(MovingTargetDefenseDNS, self).start()
        if getattr(self, "_workers_started", False):
            self.logger.warning("START: worker threads already started, skipping duplicate spawn")
            return
        self._workers_started = True
        self.threads.append(hub.spawn(self._ticker))
        self.threads.append(hub.spawn(self._rotation_loop))

    def _ticker(self):
        while True:
            self.send_event_to_observers(EventMessage("TICK"))
            hub.sleep(self.HOUSEKEEPING_INTERVAL)

    @set_ev_cls(EventMessage)
    def _housekeeping(self, ev):
        """Periodic housekeeping tasks."""
        now = time()
        # Proactive host discovery
        self._proactive_discovery(now)

        # Move VIPs from quarantine back to resources when cooldown expires
        for vip, ready_at in list(self.quarantine_until.items()):
            if ready_at <= now:
                self.quarantine_until.pop(vip, None)
                if vip not in self.Resources:
                    self.Resources.append(vip)
                    self.logger.info("QUARANTINE: VIP %s cooldown expired, returned to pool", vip)
        
        # Fallback for switches that do not reliably emit FlowRemoved on delete-by-cookie.
        # If we already requested delete and the VIP is GRACE with no controller sessions,
        # avoid stale flow refs pinning the VIP forever.
        for vip, delete_ts in list(self.vip_delete_requested_at.items()):
            if self.vip_state.get(vip) != self.VIP_STATE_GRACE:
                continue
            if self.vip_session_refs.get(vip, 0) > 0:
                continue
            if self.vip_flow_refs.get(vip, 0) <= 0:
                self.vip_delete_requested_at.pop(vip, None)
                continue
            if (now - delete_ts) >= self.VIP_INACTIVITY_RECLAIM:
                self.logger.warning(
                    "FLOW_DELETE_FALLBACK: VIP %s forcing flow refs %d->0 after delete request timeout",
                    vip,
                    self.vip_flow_refs.get(vip, 0),
                )
                self.vip_flow_refs[vip] = 0
                # CRITICAL: Touch VIP when forcing flow_refs to 0 to start inactivity timer
                # This ensures destination VIP gets reclaimed after 5s inactivity
                self._touch_vip(vip, now)
                self.vip_delete_requested_at.pop(vip, None)

        # Handle VIPs in GRACE state
        # Use flow_refs to determine activity: if flow_refs > 0, VIP is active; if flow_refs = 0, VIP is idle
        # IMPORTANT: Only process GRACE VIPs - PRIMARY VIPs should never be reclaimed
        for vip in list(self.vip_state.keys()):
            if self.vip_state.get(vip) != self.VIP_STATE_GRACE:
                continue
            
            flow_refs = self.vip_flow_refs.get(vip, 0)
            session_refs = self.vip_session_refs.get(vip, 0)
            last_seen = self.vip_last_seen.get(vip, 0)
            inactive_for = now - last_seen

            # For UDP sessions: If server VIP has no flows but client VIP (forward flow) is still active,
            # keep server VIP active. This handles cases where reverse flow expires but forward flow continues.
            has_active_udp_forward_flow = False
            if flow_refs == 0:
                for sess in self.session_table.values():
                    if (sess.get("server_reply_vip") == vip and 
                        sess.get("proto") == socket.IPPROTO_UDP and
                        sess.get("expires_at", 0) > now):
                        client_vip = sess.get("client_src_vip")
                        if client_vip and self.vip_flow_refs.get(client_vip, 0) > 0:
                            has_active_udp_forward_flow = True
                            self.logger.debug(
                                "GRACE: VIP %s (server) has active UDP forward flow (client VIP %s has %d flows), keeping active",
                                vip, client_vip, self.vip_flow_refs.get(client_vip, 0)
                            )
                            break

            if flow_refs <= 0 and session_refs <= 0 and not has_active_udp_forward_flow and inactive_for >= self.VIP_INACTIVITY_RECLAIM:
                self.logger.info("RECLAIM: VIP %s idle for %.1fs, reclaiming", vip, inactive_for)
                self._delete_flows_by_cookie(vip)
                self._reclaim_vip(vip)
            else:
                self.logger.debug(
                    "GRACE: VIP %s keep (flow_refs=%d session_refs=%d inactive_for=%.1fs has_udp_forward=%s)",
                    vip,
                    flow_refs,
                    session_refs,
                    inactive_for,
                    has_active_udp_forward_flow,
                )

        self._expire_sessions(now)
        
        # Log VIP pools
        self._log_vip_pools(now)

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

    def _ip_to_int(self, ip: str) -> int:
        p = ip.split('.')
        return (int(p[0]) << 24) + (int(p[1]) << 16) + (int(p[2]) << 8) + int(p[3])

    def _int_to_ip(self, ip_int: int) -> str:
        return ".".join([
            str((ip_int >> 24) & 0xFF),
            str((ip_int >> 16) & 0xFF),
            str((ip_int >> 8) & 0xFF),
            str(ip_int & 0xFF),
        ])

    def _host_ip_from_index(self, host_index: int) -> str:
        if host_index < 1:
            raise ValueError("host_index must be >= 1")
        return self._int_to_ip((10 << 24) + host_index)

    def _is_real_host_pool_ip(self, ip: str) -> bool:
        try:
            addr = ipaddress.ip_address(ip)
        except Exception:
            return False
        return addr in self.real_host_network

    def _vip_cookie(self, vip: str) -> int:
        return self.COOKIE_BASE | (self._ip_to_int(vip) & self.COOKIE_VIP_MASK)

    def _cookie_vip_ip(self, cookie: int) -> str:
        vip_int = cookie & self.COOKIE_VIP_MASK
        return ".".join([
            str((vip_int >> 24) & 0xFF),
            str((vip_int >> 16) & 0xFF),
            str((vip_int >> 8) & 0xFF),
            str(vip_int & 0xFF),
        ])

    def _delete_flows_by_cookie(self, vip: str):
        """Delete all flows for a VIP by matching cookie."""
        cookie = self._vip_cookie(vip)
        # Cookie mask: match COOKIE_BASE (upper 32 bits) + VIP IP (lower 32 bits)
        # Full 64-bit mask: 0xFFFF_FFFF_FFFF_FFFF to match both base and VIP IP
        cookie_mask = 0xFFFFFFFFFFFFFFFF
        
        self.vip_delete_requested_at[vip] = time()
        for dp in list(self.datapaths):
            try:
                parser = dp.ofproto_parser
                ofp = dp.ofproto
                mod = parser.OFPFlowMod(
                    datapath=dp,
                    table_id=ofp.OFPTT_ALL,
                    command=ofp.OFPFC_DELETE,
                    out_port=ofp.OFPP_ANY,
                    out_group=ofp.OFPG_ANY,
                    cookie=cookie,
                    cookie_mask=cookie_mask,
                )
                dp.send_msg(mod)
                self.logger.info("FLOW_DELETE: Deleted flows for VIP %s (cookie=0x%016x, mask=0x%016x)", 
                               vip, cookie, cookie_mask)
            except Exception as e:
                self.logger.warning("FLOW_DELETE: Failed to delete flows for VIP %s: %s", vip, e)
        # Don't reset flow_refs here - let flow removal events decrement it naturally
        # This prevents race conditions where flows are deleted but flow_refs is reset before flows actually expire

    def _add_flow(self, dp, priority, match, actions, table_id=0, idle_timeout=0, hard_timeout=0, buffer_id=None, cookie=0):
        """Install a flow rule on the switch."""
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        if buffer_id is None:
            buffer_id = ofp.OFP_NO_BUFFER
        inst = [parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions)]
        mod = parser.OFPFlowMod(
            datapath=dp,
            table_id=table_id,
            priority=priority,
            match=match,
            instructions=inst,
            cookie=cookie,
            flags=ofp.OFPFF_SEND_FLOW_REM,
            idle_timeout=idle_timeout,
            hard_timeout=hard_timeout,
            buffer_id=buffer_id,
        )
        dp.send_msg(mod)
        if cookie & self.COOKIE_BASE:
            vip = self._cookie_vip_ip(cookie)
            old_refs = self.vip_flow_refs.get(vip, 0)
            self.vip_flow_refs[vip] = old_refs + 1
            # DEBUG: log every VIP-related flow installation with match to see where
            # extra flow_refs for a given VIP (e.g., server VIP) are coming from.
            self.logger.info(
                "FLOW_ADD: vip=%s refs=%d->%d idle_timeout=%s match=%s",
                vip,
                old_refs,
                old_refs + 1,
                idle_timeout,
                match,
            )

    @set_ev_cls(ofp_event.EventOFPFlowRemoved, MAIN_DISPATCHER)
    def _flow_removed(self, ev):
        msg = ev.msg
        cookie = msg.cookie
        if not (cookie & self.COOKIE_BASE):
            return

        vip = self._cookie_vip_ip(cookie)
        if vip not in self.vip_owner:
            return

        old_refs = self.vip_flow_refs.get(vip, 0)
        self.vip_flow_refs[vip] = max(0, old_refs - 1)
        new_refs = self.vip_flow_refs.get(vip, 0)
        if new_refs <= 0:
            self.vip_delete_requested_at.pop(vip, None)
            # CRITICAL: When last flow expires, touch VIP to start inactivity timer
            # This ensures destination VIP gets reclaimed after 5s inactivity
            self._touch_vip(vip)

        self.logger.debug("FLOW_REMOVED: VIP %s flow expired (refs: %d -> %d, state=%s)", 
                         vip, old_refs, new_refs, self.vip_state.get(vip, "UNKNOWN"))
        
        # For UDP sessions: If both client and server VIPs have flow_refs == 0,
        # remove the session from the table to prevent reinstallation when late packets arrive
        if new_refs == 0:
            for key, sess in list(self.session_table.items()):
                if sess.get("proto") != socket.IPPROTO_UDP:
                    continue
                client_vip = str(sess.get("client_src_vip", ""))
                server_reply_vip = str(sess.get("server_reply_vip", ""))
                # If this VIP matches either client or server VIP, check if both are idle
                if vip == client_vip or vip == server_reply_vip:
                    client_refs = self.vip_flow_refs.get(client_vip, 0)
                    server_refs = self.vip_flow_refs.get(server_reply_vip, 0)
                    if client_refs == 0 and server_refs == 0:
                        self.logger.debug(
                            "FLOW_REMOVED: Removing UDP session (both VIPs idle: client=%s server=%s)",
                            client_vip, server_reply_vip
                        )
                        # Unpin VIPs before removing session
                        self._unpin_vip_session(client_vip)
                        self._unpin_vip_session(server_reply_vip)
                        self.session_table.pop(key, None)
                        # The partner VIP (not the one whose flow just expired) just got
                        # unpinned. If it's a GRACE VIP that's now fully idle, reclaim it
                        # immediately rather than waiting for the next housekeeping cycle.
                        partner = server_reply_vip if vip == client_vip else client_vip
                        now = time()
                        if (partner != vip
                                and self.vip_state.get(partner) == self.VIP_STATE_GRACE
                                and self.vip_flow_refs.get(partner, 0) == 0
                                and self.vip_session_refs.get(partner, 0) == 0
                                and (now - self.vip_last_seen.get(partner, 0)) >= self.VIP_INACTIVITY_RECLAIM):
                            self.logger.info("FLOW_REMOVED: VIP %s (GRACE partner) idle after session end, reclaiming", partner)
                            self._delete_flows_by_cookie(partner)
                            self._reclaim_vip(partner)
                        break
        
        # If GRACE VIP has no flows/sessions left, reclaim immediately
        if (
            self.vip_state.get(vip) == self.VIP_STATE_GRACE
            and new_refs == 0
            and self.vip_session_refs.get(vip, 0) == 0
            and (time() - self.vip_last_seen.get(vip, 0)) >= self.VIP_INACTIVITY_RECLAIM
        ):
            self.logger.info("FLOW_REMOVED: VIP %s (GRACE) now idle, reclaiming", vip)
            self._delete_flows_by_cookie(vip)
            self._reclaim_vip(vip)

    def _take_resource_vip(self) -> Optional[str]:
        """Take a VIP from the resource pool."""
        if self.Resources:
            return self.Resources.pop(0)
        return None

    def _touch_vip(self, vip: str, now: Optional[float] = None):
        if not vip:
            return
        self.vip_last_seen[vip] = now if now is not None else time()

    def _bind_primary_vip(self, host_ip: str, vip: str, now: float):
        """Bind a VIP as the primary VIP for a host."""
        self.primary_vip[host_ip] = vip
        self.vip_owner[vip] = host_ip
        self.vip_state[vip] = self.VIP_STATE_PRIMARY
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
        self.vip_created_at[vip] = now
        self._touch_vip(vip, now)
        self.host_vip_pools.setdefault(host_ip, set()).add(vip)
        self.logger.info("BIND: host=%s vip=%s", host_ip, vip)
        # Update DNS mapping file
        self._update_dns_mapping()

    def _pin_vip_session(self, vip: str):
        if not vip:
            return
        self.vip_session_refs[vip] = self.vip_session_refs.get(vip, 0) + 1

    def _unpin_vip_session(self, vip: str):
        if not vip:
            return
        self.vip_session_refs[vip] = max(0, self.vip_session_refs.get(vip, 0) - 1)

    def _deterministic_client_vip(self, client_real_ip: str) -> Optional[str]:
        """Pick deterministic source VIP for a client at session creation."""
        return self.primary_vip.get(client_real_ip)

    def _session_key(self, src_ip: str, dst_vip: str, proto: int, src_port: int, dst_port: int) -> Tuple[str, str, int, int, int]:
        return (src_ip, dst_vip, proto, src_port, dst_port)

    def _expire_sessions(self, now: float):
        """Expire controller-side sessions.

        IMPORTANT:
        - TCP sessions: we use a state machine + expires_at to drive session_refs down
          when the TCP handshake/teardown is done or idle.
        - UDP sessions: we DO NOT expire based on a fixed controller timer.
          Instead, we rely on switch flow idle_timeout + FlowRemoved to remove sessions.
          UDP sessions are pinned (session_refs > 0) but removed when both flows expire,
          at which point VIPs are unpinned. This prevents GRACE VIPs from being reclaimed
          mid-UDP stream (e.g., long iperf -u sessions).
        """
        expired = []
        for key, sess in list(self.session_table.items()):
            proto = int(sess.get("proto", 0))

            # For UDP, never expire purely on controller timer; let flows/FlowRemoved
            # drive vip_flow_refs and thus VIP reclaim.
            if proto == socket.IPPROTO_UDP:
                continue

            expires_at = sess.get("expires_at", 0)
            if expires_at <= now:
                expired.append(key)

        for key in expired:
            sess = self.session_table.pop(key, None)
            if not sess:
                continue
            # Only TCP sessions reach here; unpin both VIPs so GRACE reclaim can happen
            self._unpin_vip_session(str(sess.get("client_src_vip", "")))
            self._unpin_vip_session(str(sess.get("server_reply_vip", "")))

    def _update_tcp_session_state(self, sess: Dict[str, object], tcp_pkt: Optional[tcp.tcp], now: float) -> bool:
        if not tcp_pkt:
            return False
        bits = int(tcp_pkt.bits)
        syn = bool(bits & tcp.TCP_SYN)
        ack = bool(bits & tcp.TCP_ACK)
        fin = bool(bits & tcp.TCP_FIN)
        rst = bool(bits & tcp.TCP_RST)

        entered_closing = False
        if rst or fin:
            entered_closing = sess.get("state") != self.SESSION_TCP_CLOSING
            sess["state"] = self.SESSION_TCP_CLOSING
            sess["expires_at"] = now + self.TCP_CLOSING_TIMEOUT
        elif syn and not ack and sess.get("state") != self.SESSION_TCP_ESTABLISHED:
            sess["state"] = self.SESSION_TCP_SYN_SEEN
            sess["expires_at"] = now + self.TCP_SYN_SEEN_TIMEOUT
        else:
            sess["state"] = self.SESSION_TCP_ESTABLISHED
            sess["expires_at"] = now + self.TCP_ESTABLISHED_TIMEOUT
        return entered_closing

    def _flow_idle_timeout_for_session(self, sess: Dict[str, object]) -> int:
        proto = int(sess["proto"])
        if proto == socket.IPPROTO_UDP:
            return self.UDP_ACTIVE_TIMEOUT
        state = str(sess.get("state", self.SESSION_TCP_SYN_SEEN))
        if state == self.SESSION_TCP_CLOSING:
            return self.TCP_CLOSING_TIMEOUT
        if state == self.SESSION_TCP_ESTABLISHED:
            return self.TCP_ESTABLISHED_TIMEOUT
        return self.TCP_SYN_SEEN_TIMEOUT

    def _extract_l4_info(self, pkt, ip4) -> Optional[Dict[str, object]]:
        tcp_pkt = pkt.get_protocol(tcp.tcp)
        if tcp_pkt:
            return {
                "proto": socket.IPPROTO_TCP,
                "src_port": tcp_pkt.src_port,
                "dst_port": tcp_pkt.dst_port,
                "forward": {"ip_proto": socket.IPPROTO_TCP, "tcp_src": tcp_pkt.src_port, "tcp_dst": tcp_pkt.dst_port},
                "reverse": {"ip_proto": socket.IPPROTO_TCP, "tcp_src": tcp_pkt.dst_port, "tcp_dst": tcp_pkt.src_port},
                "tcp": tcp_pkt,
            }
        udp_pkt = pkt.get_protocol(udp.udp)
        if udp_pkt:
            return {
                "proto": socket.IPPROTO_UDP,
                "src_port": udp_pkt.src_port,
                "dst_port": udp_pkt.dst_port,
                "forward": {"ip_proto": socket.IPPROTO_UDP, "udp_src": udp_pkt.src_port, "udp_dst": udp_pkt.dst_port},
                "reverse": {"ip_proto": socket.IPPROTO_UDP, "udp_src": udp_pkt.dst_port, "udp_dst": udp_pkt.src_port},
                "tcp": None,
            }
        return None

    def _install_session_flows(self, msg, dp, parser, in_port, l4_info, sess, src_real_mac, dst_real_mac, rppt_start=None):
        """Install per-session flows for TCP/UDP.

        DEBUG: We deliberately log when flows are installed so we can see
        exactly which VIPs (client_vip / server_reply_vip) get flow_refs
        increments, and how many flows are created per session.
        """
        # CRITICAL: Prevent duplicate flow installation for the same session
        # Without this guard, every packet in a TCP/UDP stream would re-install
        # the same flows, causing vip_flow_refs to inflate (e.g., 0->1->2->3->...->9)
        # for a single session, preventing VIPs from being reclaimed.
        #
        # IMPORTANT: Once flows are installed, never reinstall them (for both TCP and UDP).
        # If flows expire (flow_refs == 0), the session is still active (session_refs > 0 for pinned sessions).
        # For both TCP and UDP: session_refs keeps VIP active even if flows expire
        if sess.get("flows_installed"):
            self.logger.debug(
                "SESSION_FLOW_SKIP: flows already installed for session "
                "(client_ip=%s server_vip=%s proto=%s src_port=%s dst_port=%s)",
                sess.get("client_real_ip"),
                sess.get("server_vip"),
                l4_info.get("proto"),
                l4_info.get("src_port"),
                l4_info.get("dst_port"),
            )
            return True

        # RPPT: use PacketIn start time so we measure PacketIn -> last FlowMod (same scope as baseline)
        if rppt_start is None:
            rppt_start = time()
        ofp = dp.ofproto
        client_ip = str(sess["client_real_ip"])
        server_vip = str(sess["server_vip"])
        client_vip = str(sess["client_src_vip"])
        server_real = str(sess["server_real_ip"])
        server_reply_vip = str(sess["server_reply_vip"])

        src_vip_mac = self._ensure_vip_mac(client_vip)
        dst_vip_mac = self._ensure_vip_mac(server_reply_vip)
        if not src_vip_mac or not dst_vip_mac:
            self.logger.warning("SESSION: Missing VIP MAC(s) for %s -> %s", client_vip, server_reply_vip)
            return False

        dst_port = self.mac_to_port.get(dp.id, {}).get(dst_real_mac, ofp.OFPP_FLOOD)
        src_port = self.mac_to_port.get(dp.id, {}).get(src_real_mac, ofp.OFPP_FLOOD)

        idle_timeout = self._flow_idle_timeout_for_session(sess)
        # DEBUG: per-session forward flow for client VIP
        self.logger.info(
            "SESSION_FLOW_ADD_FWD: client_vip=%s server_vip=%s server_reply_vip=%s idle_timeout=%s match_src=%s match_dst=%s",
            client_vip,
            server_vip,
            server_reply_vip,
            idle_timeout,
            client_ip,
            server_vip,
        )
        actions_fwd = [
            parser.OFPActionSetField(ipv4_src=client_vip),
            parser.OFPActionSetField(ipv4_dst=server_real),
            parser.OFPActionSetField(eth_src=src_vip_mac),
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(dst_port),
        ]
        match_fwd = parser.OFPMatch(
            eth_type=0x0800,
            ipv4_src=client_ip,
            ipv4_dst=server_vip,
            in_port=in_port,
            **l4_info["forward"],
        )

        self._send_packet_out(msg, dp, in_port, actions_fwd)
        self._add_flow(
            dp,
            priority=self.FLOW_PRIORITY_VIP,
            match=match_fwd,
            actions=actions_fwd,
            cookie=self._vip_cookie(client_vip),
            idle_timeout=idle_timeout,
        )

        actions_rev = [
            parser.OFPActionSetField(ipv4_src=server_reply_vip),
            parser.OFPActionSetField(ipv4_dst=client_ip),
            parser.OFPActionSetField(eth_src=dst_vip_mac),
            parser.OFPActionSetField(eth_dst=src_real_mac),
            parser.OFPActionOutput(src_port),
        ]
        match_rev = parser.OFPMatch(
            eth_type=0x0800,
            ipv4_src=server_real,
            ipv4_dst=client_vip,
            **l4_info["reverse"],
        )
        # DEBUG: per-session reverse flow for server VIP (server_reply_vip)
        self.logger.info(
            "SESSION_FLOW_ADD_REV: client_vip=%s server_vip=%s server_reply_vip=%s idle_timeout=%s match_src=%s match_dst=%s",
            client_vip,
            server_vip,
            server_reply_vip,
            idle_timeout,
            server_real,
            client_vip,
        )
        self._add_flow(
            dp,
            priority=self.FLOW_PRIORITY_VIP,
            match=match_rev,
            actions=actions_rev,
            cookie=self._vip_cookie(server_reply_vip),
            idle_timeout=idle_timeout,
        )
        # RPPT: log once per new session after last FlowMod for this provisioning event
        rppt_key = (client_ip, server_vip, l4_info.get("proto"), l4_info.get("src_port"), l4_info.get("dst_port"))
        elapsed_ms = (time() - rppt_start) * 1000
        self.logger.info("RPPT_MEASURED: key=%s elapsed_ms=%.3f", rppt_key, elapsed_ms)
        # Mark flows as installed to prevent duplicate installation on subsequent packets
        sess["flows_installed"] = True
        return True

    def _handle_l4_session(self, msg, dp, pkt, in_port, src_real, dst_vip, rppt_start=None) -> bool:
        parser = dp.ofproto_parser
        ip4 = pkt.get_protocol(ipv4.ipv4)
        if not ip4:
            return False
        l4_info = self._extract_l4_info(pkt, ip4)
        if not l4_info:
            return False

        # Handle TCP and UDP sessions (both use session table)
        proto = int(l4_info.get("proto", 0))
        real_dst = self.vip_owner.get(dst_vip)
        if not real_dst:
            return False

        src_real_mac = self.host_ip_to_mac.get(src_real)
        dst_real_mac = self.host_ip_to_mac.get(real_dst)
        if not src_real_mac or not dst_real_mac:
            return False

        now = time()
        key = self._session_key(src_real, dst_vip, proto, int(l4_info["src_port"]), int(l4_info["dst_port"]))
        sess = self.session_table.get(key)
        if not sess:
            # Don't create new sessions for GRACE VIPs with no active flows/sessions
            # This prevents late packets from creating new sessions after the original session ended
            # Check destination VIP
            if self.vip_state.get(dst_vip) == self.VIP_STATE_GRACE:
                flow_refs = self.vip_flow_refs.get(dst_vip, 0)
                session_refs = self.vip_session_refs.get(dst_vip, 0)
                self.logger.debug(
                    "SESSION: Checking GRACE VIP %s for new session (flow_refs=%d session_refs=%d)",
                    dst_vip, flow_refs, session_refs
                )
                if flow_refs == 0 and session_refs == 0:
                    self.logger.info(
                        "SESSION: Not creating new session for GRACE VIP %s (no active flows/sessions, likely late packet from %s:%s -> %s:%s)",
                        dst_vip, src_real, l4_info.get("src_port"), dst_vip, l4_info.get("dst_port")
                    )
                    return False
            
            # Also check if there's an existing session involving the destination VIP.
            # Covers the reverse-stray case: the server sends late UDP packets back to the
            # client's old GRACE VIP (which is stored as client_src_vip, not server_vip).
            if self.vip_state.get(dst_vip) == self.VIP_STATE_GRACE:
                for existing_sess in self.session_table.values():
                    if (existing_sess.get("proto") == proto and
                        (existing_sess.get("server_vip") == dst_vip or
                         existing_sess.get("server_reply_vip") == dst_vip or
                         existing_sess.get("client_src_vip") == dst_vip)):
                        self.logger.info(
                            "SESSION: Dropping late packet to GRACE VIP %s (existing session client_src_vip=%s server_vip=%s) from %s",
                            dst_vip, existing_sess.get("client_src_vip"), existing_sess.get("server_vip"), src_real
                        )
                        return False
            
            client_vip = self._deterministic_client_vip(src_real)
            if not client_vip:
                return False
            is_udp = proto == socket.IPPROTO_UDP
            sess = {
                "client_real_ip": src_real,
                "server_vip": dst_vip,
                "proto": proto,
                "client_port": int(l4_info["src_port"]),
                "server_port": int(l4_info["dst_port"]),
                "client_src_vip": client_vip,
                "server_real_ip": real_dst,
                "server_reply_vip": dst_vip,
                "state": self.SESSION_UDP_ACTIVE if is_udp else self.SESSION_TCP_SYN_SEEN,
                "expires_at": now + (self.UDP_ACTIVE_TIMEOUT if is_udp else self.TCP_SYN_SEEN_TIMEOUT),
            }
            self.session_table[key] = sess
            # IMPORTANT:
            # - For both TCP and UDP, we pin VIP sessions so GRACE VIPs are not reclaimed
            #   while sessions are active. This protects VIPs during TCP handshake/teardown
            #   and ensures UDP VIPs stay active as long as the session exists.
            self._pin_vip_session(client_vip)
            self._pin_vip_session(dst_vip)

        self._touch_vip(str(sess.get("client_src_vip", "")), now)
        self._touch_vip(str(sess.get("server_reply_vip", "")), now)

        if proto == socket.IPPROTO_UDP:
            sess["state"] = self.SESSION_UDP_ACTIVE
            sess["expires_at"] = now + self.UDP_ACTIVE_TIMEOUT
        else:
            entered_closing = self._update_tcp_session_state(sess, l4_info.get("tcp"), now)
            if entered_closing and not sess.get("flows_deleted"):
                client_vip = str(sess.get("client_src_vip", ""))
                server_reply_vip = str(sess.get("server_reply_vip", ""))
                # CRITICAL: Touch both VIPs BEFORE deleting flows to start inactivity timer
                # This ensures both VIPs get reclaimed after 5s even if FlowRemoved events are delayed
                self._touch_vip(client_vip, now)
                self._touch_vip(server_reply_vip, now)
                self._delete_flows_by_cookie(client_vip)
                if server_reply_vip != client_vip:
                    self._delete_flows_by_cookie(server_reply_vip)
                sess["flows_deleted"] = True

        if sess.get("server_real_ip") != real_dst:
            sess["server_real_ip"] = real_dst

        return self._install_session_flows(msg, dp, parser, in_port, l4_info, sess, src_real_mac, dst_real_mac, rppt_start)

    # ---------------- topology discovery ----------------

    def _topology_counts(self) -> Tuple[int, int, int]:
        num_switches = len(self.datapaths)
        num_directed_links = 0
        try:
            sw = get_switch(self, None)
            ln = get_link(self, None)
            if sw is not None:
                num_switches = len(sw)
            if ln is not None:
                num_directed_links = len(ln)
        except Exception as e:
            self.logger.debug("TOPO_DISCOVERY: topology API not ready yet: %s", e)
        num_hosts = len(self.detected_hosts)
        return num_switches, num_directed_links, num_hosts

    def _maybe_complete_discovery(self, reason: str):
        if self.discovery_completed:
            return
        num_switches, num_directed_links, num_hosts = self._topology_counts()
        switches_ok = num_switches >= self.EXPECTED_SWITCHES
        links_ok = num_directed_links >= self.EXPECTED_DIRECTED_LINKS
        hosts_ok = True if self.EXPECTED_HOSTS <= 0 else num_hosts >= self.EXPECTED_HOSTS
        if switches_ok and links_ok and hosts_ok:
            self.discovery_end_time = time()
            self.discovery_completed = True
            self.discovery_completion_reason = reason
            elapsed = self.discovery_end_time - self.discovery_start_time
            self.logger.info(
                "TOPO_DISCOVERY_COMPLETE: elapsed=%.6f s | switches=%d | directed_links=%d | reason=%s",
                elapsed, num_switches, num_directed_links, reason,
            )

    def _log_discovery_progress(self, reason: str):
        if self.discovery_completed:
            return
        num_switches, num_directed_links, num_hosts = self._topology_counts()
        elapsed = time() - self.discovery_start_time
        self.logger.info(
            "TOPO_DISCOVERY_PROGRESS: elapsed=%.6f s | switches=%d/%d | directed_links=%d/%d | reason=%s",
            elapsed, num_switches, self.EXPECTED_SWITCHES, num_directed_links, self.EXPECTED_DIRECTED_LINKS, reason,
        )

    @set_ev_cls(topo_event.EventSwitchEnter)
    def _on_topology_switch_enter(self, ev):
        self._log_discovery_progress("EventSwitchEnter")
        self._maybe_complete_discovery("EventSwitchEnter")

    @set_ev_cls(topo_event.EventLinkAdd)
    def _on_topology_link_add(self, ev):
        self._log_discovery_progress("EventLinkAdd")
        self._maybe_complete_discovery("EventLinkAdd")

    # ---------------- switch bringup ----------------

    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):
        dp = ev.msg.datapath
        self.datapaths.add(dp)
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofp.OFPP_CONTROLLER, ofp.OFPCML_NO_BUFFER)]
        self._add_flow(dp, priority=0, match=match, actions=actions, table_id=0, idle_timeout=0)
        self.logger.info("[SW] Switch %016x connected; installed table-miss", dp.id)
        self._log_discovery_progress("EventOFPSwitchFeatures")
        self._maybe_complete_discovery("EventOFPSwitchFeatures")

    # ---------------- rotation ----------------

    def _rotation_loop(self):
        while True:
            self.logger.debug("ROTATE: sleeping for %ss before next primary VIP rotation", self.ROTATE_INTERVAL)
            hub.sleep(self.ROTATE_INTERVAL)
            now = time()
            for host_ip in sorted(self.detected_hosts):
                old_vip = self.primary_vip.get(host_ip)
                new_vip = self._take_resource_vip()
                if not new_vip:
                    self.logger.warning("ROTATE: no VIP available for %s", host_ip)
                    continue
                self._bind_primary_vip(host_ip, new_vip, now)
                if old_vip and old_vip != new_vip:
                    # Safety check: Ensure old_vip was actually PRIMARY before moving to GRACE
                    if self.vip_state.get(old_vip) != self.VIP_STATE_PRIMARY:
                        self.logger.warning("ROTATE: Old VIP %s is not PRIMARY (state=%s), skipping GRACE transition",
                                           old_vip, self.vip_state.get(old_vip))
                        continue
                    
                    self.vip_state[old_vip] = self.VIP_STATE_GRACE
                    # Check if VIP is idle/active using both dataplane flows and controller sessions
                    flow_refs = self.vip_flow_refs.get(old_vip, 0)
                    session_refs = self.vip_session_refs.get(old_vip, 0)
                    if flow_refs <= 0 and session_refs <= 0:
                        self.logger.info(
                            "ROTATE: host=%s new=%s old=%s -> GRACE (idle), reclaim eligible after %ss inactivity",
                            host_ip,
                            new_vip,
                            old_vip,
                            self.VIP_INACTIVITY_RECLAIM,
                        )
                    else:
                        # VIP has active sessions/flows - keep in GRACE until both end
                        self.logger.info(
                            "ROTATE: host=%s new=%s old=%s -> GRACE (active, %d flows, %d sessions), will reclaim when flows/sessions end",
                            host_ip,
                            new_vip,
                            old_vip,
                            flow_refs,
                            session_refs,
                        )

    # ---------------- host discovery ----------------

    def _learn_host(self, pkt, dpid: int):
        """Learn host from ARP or IP packet."""
        eth_pkt = pkt.get_protocol(ethernet.ethernet)
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        real_ip, mac = None, None
        if arp_pkt:
            real_ip, mac = arp_pkt.src_ip, arp_pkt.src_mac
        elif ip_pkt and eth_pkt:
            real_ip, mac = ip_pkt.src, eth_pkt.src
        else:
            return

        if not real_ip:
            return

        # Only learn hosts from the configured real-host subnet.
        if not self._is_real_host_pool_ip(real_ip):
            return

        # Update host info
        if mac:
            self.host_ip_to_mac[real_ip] = mac

        # New host discovered
        if real_ip not in self.detected_hosts:
            self.detected_hosts.add(real_ip)
            self.host_vip_pools.setdefault(real_ip, set())
            # Assign initial primary VIP
            now = time()
            new_vip = self._take_resource_vip()
            if new_vip:
                self._bind_primary_vip(real_ip, new_vip, now)
                self.logger.info("[+] New host %s (%s) - assigned VIP: %s",
                                real_ip, mac, new_vip)

    def _send_arp_reply(self, dp, dst_mac, src_mac, src_ip, target_ip, out_port):
        """Send ARP reply."""
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        p = packet.Packet()
        p.add_protocol(ethernet.ethernet(
            ethertype=0x0806,
            dst=dst_mac,
            src=src_mac
        ))
        p.add_protocol(arp.arp(
            opcode=arp.ARP_REPLY,
            src_mac=src_mac,
            src_ip=src_ip,
            dst_mac=dst_mac,
            dst_ip=target_ip
        ))
        p.serialize()
        dp.send_msg(parser.OFPPacketOut(
            datapath=dp,
            buffer_id=ofp.OFP_NO_BUFFER,
            in_port=ofp.OFPP_CONTROLLER,
            actions=[parser.OFPActionOutput(out_port)],
            data=p.data
        ))

    def _proactive_discovery(self, now: float):
        """Proactively send ARP requests to discover hosts."""
        if not self.datapaths:
            return

        if not hasattr(self, '_last_discovery'):
            self._last_discovery = {}

        if self.REAL_HOST_POOL_SIZE <= 0:
            return

        start = self._discovery_next_host_index
        end = min(self.REAL_HOST_POOL_SIZE, start + self.PROACTIVE_DISCOVERY_BATCH - 1)

        for host_index in range(start, end + 1):
            target_ip = self._host_ip_from_index(host_index)

            if target_ip in self.detected_hosts:
                continue

            if target_ip in self._last_discovery:
                if now - self._last_discovery[target_ip] < 60:
                    continue

            self._last_discovery[target_ip] = now

            for dp in list(self.datapaths):
                try:
                    parser = dp.ofproto_parser
                    ofp = dp.ofproto
                    p = packet.Packet()
                    p.add_protocol(ethernet.ethernet(
                        ethertype=0x0806,
                        dst='ff:ff:ff:ff:ff:ff',
                        src=self.CONTROLLER_DISCOVERY_MAC
                    ))
                    p.add_protocol(arp.arp(
                        opcode=arp.ARP_REQUEST,
                        src_mac=self.CONTROLLER_DISCOVERY_MAC,
                        src_ip=self.CONTROLLER_DISCOVERY_IP,
                        dst_mac='00:00:00:00:00:00',
                        dst_ip=target_ip
                    ))
                    p.serialize()
                    dp.send_msg(parser.OFPPacketOut(
                        datapath=dp,
                        buffer_id=ofp.OFP_NO_BUFFER,
                        in_port=ofp.OFPP_CONTROLLER,
                        actions=[parser.OFPActionOutput(ofp.OFPP_FLOOD)],
                        data=p.data
                    ))
                except Exception as e:
                    self.logger.debug("Discovery ARP to %s failed: %s", target_ip, e)

        self._discovery_next_host_index = end + 1
        if self._discovery_next_host_index > self.REAL_HOST_POOL_SIZE:
            self._discovery_next_host_index = 1

    # ---------------- logging ----------------

    def _log_vip_pools(self, now: float):
        """Log VIP pools per host."""
        self.logger.info("=== VIP POOLS ===")
        
        def ipkey(ip):
            try:
                return tuple(int(x) for x in ip.split('.'))
            except Exception:
                return (ip,)

        total = 0
        active_total = 0
        for real_ip in sorted(self.detected_hosts, key=ipkey):
            pool = self.host_vip_pools.get(real_ip, set())
            if not pool:
                self.logger.info("Host %s: No VIPs assigned", real_ip)
                continue

            self.logger.info("Host %s (%d VIPs):", real_ip, len(pool))
            self.logger.info(" %-13s %-9s %-15s", "VIP", "Uptime", "State")
            self.logger.info(" %-13s %-9s %-15s", "-------------", "---------", "---------------")

            host_active = 0
            for vip in sorted(pool, key=ipkey):
                created = self.vip_created_at.get(vip, now)
                uptime = f"{max(0.0, (now - created)):.1f}s"
                state = self.vip_state.get(vip, "UNKNOWN")
                
                # Mark as ACTIVE if VIP has active flows (flow_refs > 0) OR pinned sessions (session_refs > 0)
                flow_refs = self.vip_flow_refs.get(vip, 0)
                session_refs = self.vip_session_refs.get(vip, 0)
                is_active = flow_refs > 0 or session_refs > 0
                
                # For UDP sessions: If server VIP has no flows but client VIP (forward flow) is still active,
                # mark server VIP as active. This handles cases where reverse flow expires but forward flow continues.
                if not is_active:
                    for sess in self.session_table.values():
                        if (sess.get("server_reply_vip") == vip and 
                            sess.get("proto") == socket.IPPROTO_UDP and
                            sess.get("expires_at", 0) > now):
                            client_vip = sess.get("client_src_vip")
                            if client_vip and self.vip_flow_refs.get(client_vip, 0) > 0:
                                is_active = True
                                break
                
                if is_active:
                    host_active += 1
                    active_total += 1
                    state_display = f"{state}/ACTIVE"
                else:
                    state_display = f"{state}/IDLE"
                self.logger.info(" %-13s %-9s %-15s", vip, uptime, state_display)
            total += len(pool)
            self.logger.info(" → %d active, %d idle", host_active, len(pool) - host_active)

        self.logger.info("=== SUMMARY: %d total VIPs (%d active, %d idle) ===",
                         total, active_total, total - active_total)

    # ---------------- VIP reclamation ----------------

    def _reclaim_vip(self, vip: str):
        """Reclaim a VIP and move it into quarantine before resource reuse."""
        # Safety check: Never reclaim PRIMARY VIPs - they should only be rotated
        if self.vip_state.get(vip) == self.VIP_STATE_PRIMARY:
            self.logger.warning("RECLAIM: Attempted to reclaim PRIMARY VIP %s - this should not happen! Skipping.", vip)
            return
        
        owner = self.vip_owner.pop(vip, None)
        if not owner:
            return

        if owner in self.host_vip_pools:
            self.host_vip_pools[owner].discard(vip)

        self.vip_state.pop(vip, None)
        self.vip_mac_map.pop(vip, None)
        self.vip_created_at.pop(vip, None)
        self.vip_flow_refs.pop(vip, None)
        self.vip_session_refs.pop(vip, None)
        self.vip_last_seen.pop(vip, None)
        self.vip_delete_requested_at.pop(vip, None)

        if self.primary_vip.get(owner) == vip:
            self.primary_vip.pop(owner, None)

        self.quarantine_until[vip] = time() + self.VIP_QUARANTINE_SECONDS

        self.logger.info("RECLAIM: VIP %s from host %s -> quarantine %ss", vip, owner, self.VIP_QUARANTINE_SECONDS)
        # Update DNS mapping file
        self._update_dns_mapping()

    def _update_dns_mapping(self):
        """
        Update DNS mapping file for DNS server.
        
        Creates mapping: {"real_ip": "primary_vip", ...}
        Example: {"10.0.0.1": "10.0.0.51", "10.0.0.2": "10.0.0.52"}
        
        DNS server reads this file to resolve hostnames (h1, h2, etc.) to
        current PRIMARY VIPs. This file is updated:
        - When VIP is bound (initial assignment)
        - When VIP rotates (every 60s)
        - When VIP is reclaimed
        
        DNS server reloads this file on each query to always return the latest
        PRIMARY VIPs, which rotate every ROTATE_INTERVAL (60s).
        """
        import json
        import os
        
        # Map real IPs to their current PRIMARY VIPs
        mapping = {}
        for host_ip, vip in self.primary_vip.items():
            if vip:  # Only include hosts with active PRIMARY VIPs
                mapping[host_ip] = vip
        
        # Write to shared file (adjust path for Windows if needed)
        mapping_file = "/tmp/mtd_vip_mapping.json"
        if os.name == 'nt':  # Windows
            mapping_file = os.path.join(os.environ.get('TEMP', 'C:\\temp'), 'mtd_vip_mapping.json')
        
        try:
            os.makedirs(os.path.dirname(mapping_file), exist_ok=True)
            with open(mapping_file, 'w') as f:
                json.dump(mapping, f)
            self.logger.debug("DNS: Updated mapping file with %d entries: %s", len(mapping), mapping)
        except Exception as e:
            self.logger.warning("DNS: Failed to update mapping file: %s", e)

    # ---------------- packet handling ----------------

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in(self, ev):
        # RPPT: start timing at PacketIn (same as baseline) so both measure PacketIn -> FlowMod
        rppt_start = time()
        msg = ev.msg
        dp = msg.datapath
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        in_port = msg.match['in_port']
        dpid = dp.id

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocol(ethernet.ethernet)
        if not eth:
            return

        self.mac_to_port.setdefault(dpid, {})
        self.mac_to_port[dpid][eth.src] = in_port

        # Handle ARP
        arp_pkt = pkt.get_protocol(arp.arp)
        if arp_pkt:
            self._learn_host(pkt, dpid)
            self._handle_arp(msg, dp, pkt, arp_pkt, eth, in_port, dpid)
            return

        # Handle IP packets
        ip4 = pkt.get_protocol(ipv4.ipv4)
        if not ip4:
            return

        self._learn_host(pkt, dpid)
        src_ip, dst_ip = ip4.src, ip4.dst

        # DNS-based approach: 
        # - Hosts resolve destinations to VIPs via DNS
        # - Hosts send: src=real_ip, dst=VIP
        # - Controller does SNAT (real→VIP) and DNAT (VIP→real)
        # - Much simpler than original: no complex session tracking
        
        src_is_real = src_ip in self.detected_hosts
        dst_is_real = dst_ip in self.detected_hosts
        dst_is_vip = dst_ip in self.vip_owner
        src_is_vip = src_ip in self.vip_owner

        # Real host → Real host: Translate both to VIPs (when hosts use real IPs directly)
        if src_is_real and dst_is_real:
            self._handle_real_to_real(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
            return

        # Real host → VIP: SNAT + DNAT (when DNS resolves to VIP)
        if src_is_real and dst_is_vip:
            self._handle_real_to_vip(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip, rppt_start)
            return

        # VIP → Real host: Reverse SNAT (reply path)
        if src_is_vip and src_ip in self.vip_owner:
            self._handle_vip_to_real(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
            return

        # VIP → VIP: Both already translated
        if src_is_vip and dst_is_vip:
            self._handle_vip_to_vip(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
            return

        # Unknown: forward as-is
        self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)

    def _handle_arp(self, msg, dp, pkt, arp_pkt, eth, in_port, dpid):
        """Handle ARP packets."""
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        if arp_pkt.opcode == arp.ARP_REQUEST:
            target_ip = arp_pkt.dst_ip

            # Check if request is for a VIP
            if target_ip in self.vip_owner:
                vip_mac = self.vip_mac_map.get(target_ip)
                if vip_mac:
                    self._send_arp_reply(
                        dp, eth.src, vip_mac, target_ip, arp_pkt.src_ip, in_port
                    )
                    self.logger.debug("ARP: replied VIP %s -> %s", target_ip, vip_mac)
                return

            # Forward ARP requests for real hosts (let them resolve normally)
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        # Forward ARP replies
        out_port = self.mac_to_port.get(dpid, {}).get(eth.dst, ofp.OFPP_FLOOD)
        self._forward_packet(msg, dp, in_port, dpid, eth.dst, out_port)

    def _handle_real_to_real(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_real, dst_real):
        """
        Handle traffic between two real hosts: translate both to PRIMARY VIPs.
        This handles cases where hosts use real IPs directly (not DNS).
        """
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        # Get PRIMARY VIPs for both hosts
        src_vip = self.primary_vip.get(src_real)
        dst_vip = self.primary_vip.get(dst_real)

        if not src_vip or not dst_vip:
            self.logger.warning("REAL-TO-REAL: Missing VIP for src=%s or dst=%s", src_real, dst_real)
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        src_vip_mac = self._ensure_vip_mac(src_vip)
        dst_vip_mac = self._ensure_vip_mac(dst_vip)
        dst_real_mac = self.host_ip_to_mac.get(dst_real)

        if not src_vip_mac:
            self.logger.warning("REAL-TO-REAL: Missing VIP MAC for src_vip=%s", src_vip)
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        if not dst_real_mac:
            self.logger.debug("REAL-TO-REAL: Destination MAC unknown for %s, flooding", dst_real)
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        dst_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)

        # SNAT + DNAT: real → VIP (both directions)
        actions = [
            parser.OFPActionSetField(ipv4_src=src_vip),  # SNAT: real → VIP
            parser.OFPActionSetField(ipv4_dst=dst_real),  # Keep destination as real IP
            parser.OFPActionSetField(eth_src=src_vip_mac),
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(dst_port)
        ]

        forward_l4_match, reverse_l4_match = self._extract_l4_match_fields(pkt, ip4)

        # Protocol-aware match: src=real, dst=real + L4 fields when available
        match = parser.OFPMatch(
            eth_type=0x0800,
            ipv4_src=src_real,
            ipv4_dst=dst_real,
            in_port=in_port,
            **forward_l4_match,
        )

        # Send first packet immediately (critical for TCP SYN)
        self._send_packet_out(msg, dp, in_port, actions)
        # ICMP error messages should not count toward VIP activity (flow_refs)
        # They're transient error responses, not actual session traffic
        cookie = 0 if self._is_icmp_error(pkt) else self._vip_cookie(src_vip)
        # Install flow for subsequent packets
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                      cookie=cookie, idle_timeout=5)
        self.logger.debug("REAL-TO-REAL: Installed forward flow for TCP/UDP: %s -> %s (VIP: %s -> %s)", 
                         src_real, dst_real, src_vip, dst_real)

        # Install reverse flow: dst_real → src_vip (reply path)
        # Forward flow sends to real host: src=src_vip, dst=dst_real
        # Real host receives and replies: src=dst_real, dst=src_vip (replies to VIP it received)
        # We need to match this and translate: src=dst_real→dst_vip, dst=src_vip→src_real
        # CRITICAL: Reverse flow must be installed with dst_vip cookie to track flow_refs for destination VIP
        src_real_mac = self.host_ip_to_mac.get(src_real) or eth.src
        if src_real_mac:
            self.host_ip_to_mac[src_real] = src_real_mac
        if not dst_vip_mac:
            self.logger.error("REAL-TO-REAL: Missing dst_vip_mac for %s (dst_vip=%s), cannot install reverse flow! dst VIP flow_refs will not be tracked!", 
                             dst_real, dst_vip)
        if not src_real_mac:
            self.logger.error("REAL-TO-REAL: Missing src_real_mac for %s, cannot install reverse flow!", src_real)
        if src_real_mac and dst_vip_mac:
            src_port = self.mac_to_port.get(dpid, {}).get(src_real_mac, ofp.OFPP_FLOOD)
            actions_rev = [
                # Translate reply source to VIP so host sees VIP in replies
                parser.OFPActionSetField(ipv4_src=dst_vip),  # SNAT: real → VIP (so host sees VIP in reply)
                parser.OFPActionSetField(ipv4_dst=src_real),  # DNAT: VIP → real (so host receives it)
                parser.OFPActionSetField(eth_src=dst_vip_mac),
                parser.OFPActionSetField(eth_dst=src_real_mac),
                parser.OFPActionOutput(src_port)
            ]
            # Match reply: src=dst_real, dst=src_vip (real host replies to VIP it received)
            # Note: Don't constrain in_port - reply may come from different switch/port
            match_rev = parser.OFPMatch(
                eth_type=0x0800,
                ipv4_src=dst_real,
                ipv4_dst=src_vip,  # Real host replies to VIP (the source VIP it received)
                **reverse_l4_match,
            )
            # Reverse flow translates source to dst_vip, so use dst_vip cookie to track flow_refs
            # ICMP error messages should not count toward VIP activity (flow_refs)
            cookie_rev = 0 if self._is_icmp_error(pkt) else self._vip_cookie(dst_vip)
            self.logger.debug("REAL-TO-REAL: Installing reverse flow for dst_vip=%s (cookie=0x%016x) to track flow_refs", 
                             dst_vip, cookie_rev)
            self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match_rev, actions=actions_rev,
                          cookie=cookie_rev, idle_timeout=5)

        self.logger.debug("REAL-TO-REAL: %s -> %s (translated to %s -> %s)", 
                         src_real, dst_real, src_vip, dst_real)

    def _handle_real_to_vip(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_real, dst_vip, rppt_start=None):
        """
        Handle traffic from real host to VIP: SNAT + DNAT.
        Simplified version - no complex session tracking.
        """
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        # Get source VIP for SNAT
        src_vip = self.primary_vip.get(src_real)
        if not src_vip:
            self.logger.warning("REAL-TO-VIP: No VIP for source %s", src_real)
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        # Get real destination
        real_dst = self.vip_owner.get(dst_vip)
        if not real_dst:
            self.logger.warning("REAL-TO-VIP: No owner for VIP %s", dst_vip)
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        src_vip_mac = self._ensure_vip_mac(src_vip)
        dst_vip_mac = self._ensure_vip_mac(dst_vip)
        dst_real_mac = self.host_ip_to_mac.get(real_dst)
        
        if not src_vip_mac or not dst_real_mac:
            self.logger.debug("REAL-TO-VIP: Missing MACs, flooding")
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        # Try to handle as L4 session first (TCP/UDP).
        # _handle_l4_session returns True  → session flows installed, we're done.
        # _handle_l4_session returns False → either not TCP/UDP (ICMP etc), OR it's TCP/UDP
        #   but was deliberately blocked (e.g. late stray packet to a GRACE VIP).
        #   In the blocked case we must NOT fall through to the generic flow installer.
        is_l4 = (pkt.get_protocol(udp.udp) is not None or
                 pkt.get_protocol(tcp.tcp) is not None)
        if self._handle_l4_session(msg, dp, pkt, in_port, src_real, dst_vip, rppt_start):
            return
        if is_l4:
            # TCP/UDP packet blocked by session guard — drop, no generic flows
            return

        # Only install flows for non-TCP/UDP traffic (e.g., ICMP/ping)
        dst_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)
        
        # SNAT + DNAT: real → VIP (both directions)
        actions = [
            parser.OFPActionSetField(ipv4_src=src_vip),  # SNAT
            parser.OFPActionSetField(ipv4_dst=real_dst),  # DNAT
            parser.OFPActionSetField(eth_src=src_vip_mac),
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(dst_port)
        ]

        forward_l4_match, reverse_l4_match = self._extract_l4_match_fields(pkt, ip4)

        # Protocol-aware match: src=real, dst=VIP + L4 fields when available
        match = parser.OFPMatch(
            eth_type=0x0800,
            ipv4_src=src_real,
            ipv4_dst=dst_vip,
            in_port=in_port,
            **forward_l4_match,
        )
        
        # Send first packet immediately (critical for TCP SYN)
        self._send_packet_out(msg, dp, in_port, actions)
        # ICMP error messages should not count toward VIP activity (flow_refs)
        # They're transient error responses, not actual session traffic
        cookie = 0 if self._is_icmp_error(pkt) else self._vip_cookie(src_vip)
        # Use shorter timeout for ICMP (TCP/UDP handled by session flows above)
        idle_timeout = 5
        # Install flow for subsequent packets
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                      cookie=cookie, idle_timeout=idle_timeout)
        self.logger.debug("REAL-TO-VIP: Installed forward flow for ICMP: %s -> %s (VIP: %s -> %s)", 
                         src_real, dst_vip, src_vip, real_dst)
        
        # Install reverse flow: real_dst → src_vip (reply path)
        # Forward flow sends to real host: src=src_vip, dst=real_dst
        # Real host receives and replies: src=real_dst, dst=src_vip (replies to VIP it received)
        # We need to match this and translate: src=real_dst→dst_vip, dst=src_vip→src_real
        src_real_mac = self.host_ip_to_mac.get(src_real) or eth.src
        if src_real_mac:
            self.host_ip_to_mac[src_real] = src_real_mac
        if not dst_vip_mac:
            self.logger.error("REAL-TO-VIP: Missing dst_vip_mac for dst_vip=%s, cannot install reverse flow", dst_vip)
        if not src_real_mac:
            self.logger.error("REAL-TO-VIP: Missing src_real_mac for %s, cannot install reverse flow", src_real)
        if src_real_mac and dst_vip_mac:
            src_port = self.mac_to_port.get(dpid, {}).get(src_real_mac, ofp.OFPP_FLOOD)
            actions_rev = [
                # Translate reply source to VIP so host sees VIP in replies
                parser.OFPActionSetField(ipv4_src=dst_vip),  # SNAT: real → VIP (so host sees VIP in reply)
                parser.OFPActionSetField(ipv4_dst=src_real),  # DNAT: VIP → real (so host receives it)
                parser.OFPActionSetField(eth_src=dst_vip_mac),
                parser.OFPActionSetField(eth_dst=src_real_mac),
                parser.OFPActionOutput(src_port)
            ]
            # Match reply: src=real_dst, dst=src_vip (real host replies to VIP it received)
            # Note: Don't constrain in_port - reply may come from different switch/port
            match_rev = parser.OFPMatch(
                eth_type=0x0800,
                ipv4_src=real_dst,
                ipv4_dst=src_vip,  # Real host replies to VIP (the source VIP it received)
                **reverse_l4_match,
            )
            # Reverse flow translates source to dst_vip, so use dst_vip cookie to track flow_refs
            # ICMP error messages should not count toward VIP activity (flow_refs)
            cookie_rev = 0 if self._is_icmp_error(pkt) else self._vip_cookie(dst_vip)
            self.logger.debug("REAL-TO-VIP: Installing reverse flow for dst_vip=%s (cookie=0x%016x) to track flow_refs", 
                             dst_vip, cookie_rev)
            self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match_rev, actions=actions_rev,
                          cookie=cookie_rev, idle_timeout=5)
        
        self.logger.debug("REAL-TO-VIP: %s -> %s (translated to %s -> %s)", 
                         src_real, dst_vip, src_vip, real_dst)

    def _handle_vip_to_real(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_vip, dst_real):
        """
        Handle traffic from VIP to real host: reverse SNAT.
        This is the reply path.
        """
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        if src_vip not in self.vip_owner:
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        dst_real_mac = self.host_ip_to_mac.get(dst_real)
        if not dst_real_mac:
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        # Check if this is TCP/UDP - if so, session flows already handle it
        l4_info = self._extract_l4_info(pkt, ip4)
        if l4_info:
            # TCP/UDP packet - session flows are already installed by _install_session_flows
            # Just forward the packet, don't install additional flows
            dst_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)
            actions = [
                parser.OFPActionSetField(eth_dst=dst_real_mac),
                parser.OFPActionOutput(dst_port)
            ]
            self._send_packet_out(msg, dp, in_port, actions)
            self.logger.debug("VIP-TO-REAL: TCP/UDP packet, session flows handle it, skipping duplicate flow installation")
            return

        # Only install flows for non-TCP/UDP traffic (e.g., ICMP/ping)
        # TCP/UDP flows are handled by _install_session_flows
        dst_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)
        actions = [
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(dst_port)
        ]

        forward_l4_match, _ = self._extract_l4_match_fields(pkt, ip4)

        match = parser.OFPMatch(
            eth_type=0x0800,
            ipv4_src=src_vip,
            ipv4_dst=dst_real,
            in_port=in_port,
            **forward_l4_match,
        )
        
        self._send_packet_out(msg, dp, in_port, actions)
        # ICMP error messages should not count toward VIP activity (flow_refs)
        # They're transient error responses, not actual session traffic
        cookie = 0 if self._is_icmp_error(pkt) else self._vip_cookie(src_vip)
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                      cookie=cookie, idle_timeout=5)
        
        self.logger.debug("VIP-TO-REAL: %s (VIP) -> %s", src_vip, dst_real)

    def _handle_vip_to_vip(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_vip, dst_vip):
        """
        Handle traffic between VIPs: both already translated.
        """
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        real_dst = self.vip_owner.get(dst_vip)
        if not real_dst:
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        dst_real_mac = self.host_ip_to_mac.get(real_dst)
        if not dst_real_mac:
            self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)
            return

        # Just DNAT: VIP → real
        dst_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)
        actions = [
            parser.OFPActionSetField(ipv4_dst=real_dst),  # DNAT only
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(dst_port)
        ]

        forward_l4_match, _ = self._extract_l4_match_fields(pkt, ip4)

        match = parser.OFPMatch(
            eth_type=0x0800,
            ipv4_src=src_vip,
            ipv4_dst=dst_vip,
            in_port=in_port,
            **forward_l4_match,
        )
        
        self._send_packet_out(msg, dp, in_port, actions)
        # ICMP error messages should not count toward VIP activity (flow_refs)
        # They're transient error responses, not actual session traffic
        cookie = 0 if self._is_icmp_error(pkt) else self._vip_cookie(dst_vip)
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                      cookie=cookie, idle_timeout=5)

    def _is_icmp_error(self, pkt) -> bool:
        """Check if ICMP packet is an error message (not echo request/reply)."""
        icmp_pkt = pkt.get_protocol(icmp.icmp)
        if not icmp_pkt:
            return False
        # ICMP error messages: Destination Unreachable (3), Time Exceeded (11), 
        # Parameter Problem (12), Source Quench (4 - deprecated)
        # Echo Request (8) and Echo Reply (0) are NOT errors
        return icmp_pkt.type not in (icmp.ICMP_ECHO_REQUEST, icmp.ICMP_ECHO_REPLY)

    def _extract_l4_match_fields(self, pkt, ip4):
        """Build protocol-aware OpenFlow match fields for forward and reverse directions."""
        tcp_pkt = pkt.get_protocol(tcp.tcp)
        if tcp_pkt:
            return (
                {"ip_proto": socket.IPPROTO_TCP, "tcp_src": tcp_pkt.src_port, "tcp_dst": tcp_pkt.dst_port},
                {"ip_proto": socket.IPPROTO_TCP, "tcp_src": tcp_pkt.dst_port, "tcp_dst": tcp_pkt.src_port},
            )

        udp_pkt = pkt.get_protocol(udp.udp)
        if udp_pkt:
            return (
                {"ip_proto": socket.IPPROTO_UDP, "udp_src": udp_pkt.src_port, "udp_dst": udp_pkt.dst_port},
                {"ip_proto": socket.IPPROTO_UDP, "udp_src": udp_pkt.dst_port, "udp_dst": udp_pkt.src_port},
            )

        icmp_pkt = pkt.get_protocol(icmp.icmp)
        if icmp_pkt:
            reverse_type = icmp_pkt.type
            if icmp_pkt.type == icmp.ICMP_ECHO_REQUEST:
                reverse_type = icmp.ICMP_ECHO_REPLY
            elif icmp_pkt.type == icmp.ICMP_ECHO_REPLY:
                reverse_type = icmp.ICMP_ECHO_REQUEST

            return (
                {
                    "ip_proto": socket.IPPROTO_ICMP,
                    "icmpv4_type": icmp_pkt.type,
                    "icmpv4_code": icmp_pkt.code,
                },
                {
                    "ip_proto": socket.IPPROTO_ICMP,
                    "icmpv4_type": reverse_type,
                    "icmpv4_code": icmp_pkt.code,
                },
            )

        return ({"ip_proto": ip4.proto}, {"ip_proto": ip4.proto})

    def _ensure_vip_mac(self, vip: str) -> Optional[str]:
        """Return VIP MAC, generating and caching one if missing."""
        if not vip:
            return None
        vip_mac = self.vip_mac_map.get(vip)
        if vip_mac:
            return vip_mac
        vip_mac = self._generate_vip_mac(vip)
        self.vip_mac_map[vip] = vip_mac
        self.logger.warning("VIP_MAC: generated missing MAC mapping for VIP %s -> %s", vip, vip_mac)
        return vip_mac

    def _forward_packet(self, msg, dp, in_port, dpid, dst_mac, out_port):
        """Forward packet without modification."""
        parser = dp.ofproto_parser
        actions = [parser.OFPActionOutput(out_port)]
        self._send_packet_out(msg, dp, in_port, actions)

    def _send_packet_out(self, msg, dp, in_port, actions):
        """Send packet-out message."""
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        data = msg.data if msg.buffer_id == ofp.OFP_NO_BUFFER else None
        out = parser.OFPPacketOut(
            datapath=dp,
            buffer_id=msg.buffer_id,
            in_port=in_port,
            actions=actions,
            data=data,
        )
        dp.send_msg(out)
