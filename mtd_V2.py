"""
Moving Target Defense Ryu controller with dynamic VIP rotation and reply locking.
Rewritten from scratch to preserve legacy logging semantics while adding
per-packet randomized outbound VIP selection, reply VIP locking, and
comprehensive housekeeping.
"""

import json
import random
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
    SESSION_NO_GROWTH_TIMEOUT = 15   # session "quiet" threshold (s)
    HOUSEKEEPING_INTERVAL = 15        # periodic tick (s)
    DISCOVERY_RANGE_LAST_OCTET_MAX = 10   # discover 10.0.0.1..10.0.0.10
    VIP_POOL_START = "10.0.0.11"         # first VIP (avoid clashing with discovered hosts)

    INITIAL_ASSIGN_ON_DISCOVERY = True

    ICMP_INSTALL_FLOWS = False
    ICMP_FLOW_IDLE = 5
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
        self.host_primary_vip: Dict[str, Optional[str]] = {}
        self.host_primary_assigned_at: Dict[str, float] = {}
        self.host_primary_active_since: Dict[str, float] = {}

    # ---------------- lifecycle ----------------
    def start(self):
        super(MovingTargetDefense, self).start()
        self.threads.append(hub.spawn(self._ticker))

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
        # intentionally minimal logging; callers manage rotation decisions

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

        # 2) evaluate each host for rotation and cleanup
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
        pool = self.host_vip_pools.get(real_ip, set())
        primary = self.host_primary_vip.get(real_ip)
        primary_active = bool(primary and self.vip_active_sessions.get(primary))

        if primary_active:
            if self.host_primary_active_since.get(real_ip) is None:
                self.host_primary_active_since[real_ip] = now
            elif (now - self.host_primary_active_since[real_ip]) >= self.VIP_ROTATION_INTERVAL:
                self._rotate_host_vip(real_ip, now)
        else:
            self.host_primary_active_since.pop(real_ip, None)
            if primary and not self.vip_active_sessions.get(primary):
                self._reclaim_vip(primary, rebalance=False)
                primary = self.host_primary_vip.get(real_ip)

        # Reclaim any non-primary VIPs that no longer service sessions.
        for vip in list(pool):
            if vip == self.host_primary_vip.get(real_ip):
                continue
            if self.vip_active_sessions.get(vip):
                continue
            self._reclaim_vip(vip, rebalance=False)

        # If the host still has active sessions, ensure a primary exists.
        if self.host_active_sessions.get(real_ip):
            self._ensure_primary_vip(real_ip, now, force=True)
        else:
            # Host is idle; release the primary so the next session gets a fresh VIP.
            primary = self.host_primary_vip.get(real_ip)
            if primary and not self.vip_active_sessions.get(primary):
                self._reclaim_vip(primary, rebalance=False)

    def _ensure_primary_vip(self, real_ip: str, now: float, *, force: bool = False) -> Optional[str]:
        pool = self.host_vip_pools.setdefault(real_ip, set())
        primary = self.host_primary_vip.get(real_ip)

        if primary and primary in pool:
            return primary

        if not force and not self.host_active_sessions.get(real_ip):
            return None

        if pool:
            newest = max(
                pool,
                key=lambda vip: self.vip_last_activity.get(vip, self.vip_created_at.get(vip, 0.0)),
            )
            self.host_primary_vip[real_ip] = newest
            self.host_primary_assigned_at[real_ip] = now
            self.host_primary_active_since.pop(real_ip, None)
            return newest

        vip = self._allocate_vip_to_host(real_ip, now, announce=True, make_primary=True)
        if vip:
            self.host_primary_assigned_at[real_ip] = now
            self.host_primary_active_since.pop(real_ip, None)
        return vip

    def _take_resource_vip(self, now: float) -> Optional[str]:
        if not self.Resources:
            return None
        return self.Resources.pop(0)

    def _rotate_host_vip(self, real_ip: str, now: float) -> None:
        current = self.host_primary_vip.get(real_ip)
        new_vip = self._allocate_vip_to_host(real_ip, now, announce=True, make_primary=True)
        if not new_vip:
            return
        self.host_primary_assigned_at[real_ip] = now
        self.host_primary_active_since.pop(real_ip, None)
        self.logger.info("ROTATE: host %s primary VIP -> %s (prev=%s)", real_ip, new_vip, current)
        if current:
            # When the previous VIP finishes serving sessions it will be reclaimed
            # by the trimming logic.
            pass

    def _bind_vip_to_host(self, vip: str, real_ip: str, now: float, *, make_primary: bool = False) -> None:
        self.V2R_Mappings[vip] = real_ip
        self.host_vip_pools.setdefault(real_ip, set()).add(vip)
        self.vip_created_at[vip] = now
        self.vip_last_seen[vip] = now
        self.vip_last_activity[vip] = now
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
        self._purge_flows_for_vip(vip)
        if make_primary or self.host_primary_vip.get(real_ip) is None:
            self.host_primary_vip[real_ip] = vip
            self.host_primary_assigned_at[real_ip] = now
            self.host_primary_active_since.pop(real_ip, None)

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
                host_sessions = self.host_active_sessions.setdefault(host, set())
                host_sessions.add(session_key)
                affected_hosts.add(host)
            for host in affected_hosts:
                self._rebalance_host_vips(host, now)

        vip_dst = None
        forward_dst_mac = None

        if dst_ip in self.V2R_Mappings:
            vip_dst = dst_ip
            real_dst = self.V2R_Mappings[dst_ip]
            actions.append(parser.OFPActionSetField(ipv4_dst=real_dst))
            dst_mac = self.host_ip_to_mac.get(real_dst)
            if dst_mac:
                actions.append(parser.OFPActionSetField(eth_dst=dst_mac))
                forward_dst_mac = dst_mac
            session.vip_dst = vip_dst
            session.last_contacted_vip = vip_dst
            # If replies were previously using a different VIP, detach it so a
            # reclaimed VIP cannot linger as the preferred reverse mapping.
            if session.last_reply_vip and session.last_reply_vip != vip_dst:
                released = self._detach_session_from_vip(session.last_reply_vip, session_key)
                if released:
                    owner = self.V2R_Mappings.get(session.last_reply_vip)
                    if owner:
                        self._evaluate_host_state(owner, now)
                session.last_reply_vip = None
            if proto != 1 and not session.vip_locked:
                session.vip_locked = vip_dst
            self._touch_vip(vip_dst, now, "session create: vip_dst")
            if new_session:
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
            previous_vip_src = None

            if binding_vip and vip_src and vip_src != binding_vip:
                previous_vip_src = vip_src
                previous_target = session.active_target_vip
                self._detach_session_from_vip(previous_vip_src, session_key)
                owner = self.V2R_Mappings.get(previous_vip_src)
                if owner:
                    self._evaluate_host_state(owner, now)
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
                self._activate_vip_for_session(vip_src, session_key, now)
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
                        self._activate_vip_for_session(vip_src, session_key, now)
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
                self._detach_session_from_vip(previous_vip_src, session_key)
                owner = self.V2R_Mappings.get(previous_vip_src)
                if owner:
                    self._evaluate_host_state(owner, now)
                if previous_target:
                    session.vip_src_by_target.pop(previous_target, None)
                session.vip_src = None
                session.active_target_vip = None
                vip_src = None

            if need_new_vip:
                vip_src = self._choose_outbound_vip(client_real, now)
                if not vip_src:
                    vip_src = self._allocate_vip_to_host(client_real, now, announce=True)
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
                    self._activate_vip_for_session(vip_src, session_key, now)
                    self._touch_vip(vip_src, now, "session create: vip_src")
                    self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
                    session.last_vip_src_announce = now
                    self._evaluate_host_state(client_real, now)

            if not session.vip_src:
                pool = list(self.host_vip_pools.get(client_real, set()))
                if pool:
                    vip_src = random.choice(pool)
                    session.vip_src = vip_src
                    session.active_target_vip = vip_dst
                    if vip_dst:
                        session.vip_src_by_target[vip_dst] = vip_src
                    session.last_vip_src_use = now
                    self._activate_vip_for_session(vip_src, session_key, now)
                    self._touch_vip(vip_src, now, "fallback vip_src assign")
                    # ensure peer learns the VIP MAC before packets flow
                    self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
                    session.last_vip_src_announce = now
                    self._evaluate_host_state(client_real, now)

            if session.vip_src:
                mac = self.vip_mac_map.get(session.vip_src) or self._generate_vip_mac(session.vip_src)
                self.vip_mac_map[session.vip_src] = mac
                actions.append(parser.OFPActionSetField(ipv4_src=session.vip_src))
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

            if proto == 1:
                preferred_vips: List[Optional[str]] = [icmp_bound_vip, mapping_vip, session.last_reply_vip]
                for candidate in preferred_vips:
                    if candidate and self.V2R_Mappings.get(candidate) == server_real:
                        vip_src = candidate
                        break
            else:
                ordered: List[Optional[str]] = [session.vip_locked, mapping_vip,
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
                pool = self.host_vip_pools.get(server_real, set())
                for candidate in sorted(pool):
                    if self.V2R_Mappings.get(candidate) == server_real:
                        vip_src = candidate
                        break

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
            host_sessions = self.host_active_sessions.get(host)
            if host_sessions and session_key in host_sessions:
                host_sessions.discard(session_key)
                if not host_sessions:
                    self.host_active_sessions.pop(host, None)
                affected_hosts.add(host)
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

    def _choose_outbound_vip(self, real_ip: str, now: float) -> Optional[str]:
        return self._ensure_primary_vip(real_ip, now, force=True)

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
        # self.logger.info("REPLY MAPPING: server=%s client=%s proto=%d uses VIP %s (5tuple key=%s)",
        #                  server_real, client_real, proto, vip_dst, key)

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
        mac = self.vip_mac_map.get(vip)
        if not mac:
            mac = self._generate_vip_mac(vip)
            # do not persist the MAC here; callers will record authoritative
            # bindings during assignment/announcement.

        flow_matches = [
            {"eth_type": 0x0800, "ipv4_dst": vip},
            {"eth_type": 0x0800, "ipv4_src": vip},
        ]

        # Some switches learn MAC based forwarding rules from earlier traffic.
        # When a VIP is rebound we must tear down those flows as well or packets
        # may continue to follow the stale output port until the rule times out.
        if mac:
            flow_matches.extend([
                {"eth_dst": mac},
                {"eth_src": mac},
            ])

        for dp in list(self.datapaths):
            parser = dp.ofproto_parser
            ofp = dp.ofproto
            for match_kwargs in flow_matches:
                match = parser.OFPMatch(**match_kwargs)
                mod = parser.OFPFlowMod(
                    datapath=dp,
                    table_id=ofp.OFPTT_ALL,
                    command=ofp.OFPFC_DELETE,
                    out_port=ofp.OFPP_ANY,
                    out_group=ofp.OFPG_ANY,
                    match=match,
                )
                dp.send_msg(mod)

            # Ensure the controller receives notification once the deletions are
            # processed so newly arriving packets hit the table-miss path
            # immediately instead of waiting for idle timers.
            try:
                barrier = parser.OFPBarrierRequest(dp)
                dp.send_msg(barrier)
            except Exception:
                # Barrier support is optional; fall back silently if the switch
                # rejects the request.  A warning would be too noisy here.
                pass

        self.logger.info(
            "FLOW: purged flows for VIP %s (IP & MAC matches removed)",
            vip,
        )

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
        if self.host_primary_vip.get(real_ip) == vip:
            self.host_primary_vip.pop(real_ip, None)
            self.host_primary_assigned_at.pop(real_ip, None)
            self.host_primary_active_since.pop(real_ip, None)
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
        self._purge_flows_for_vip(vip)
        if vip not in self.Resources:
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
                if self.vip_active_sessions.get(vip):
                    state = "ACTIVE"
                    idle_str = "-"
                    recl_str = "-"
                    host_active += 1
                    active_total += 1
                else:
                    state = "IDLE"
                    if last is not None:
                        idle_str = f"{max(0.0, now - last):.1f}s"
                    else:
                        idle_str = "-"
                    recl_str = "-"
                self.logger.info(" %-13s %-9s %-8s %-10s %-12s", vip, uptime, state, idle_str, recl_str)
                total += 1
            self.logger.info(" → %d active, %d idle", host_active, len(pool) - host_active)
        self.logger.info("=== SUMMARY: %d total VIPs (%d active, %d idle) ===",
                         total, active_total, total - active_total)
