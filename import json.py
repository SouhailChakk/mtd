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
    NUM_VIPS = 246                   # VIP pool, starting at 10.0.0.9
    VIPS_PER_HOST = 5                # per-host target
    VIP_IDLE_TIMEOUT = 60            # reclaim after this idle grace (s)
    SESSION_NO_GROWTH_TIMEOUT = 15   # session "quiet" threshold (s)
    HOUSEKEEPING_INTERVAL = 15        # periodic tick (s)
    DISCOVERY_RANGE_LAST_OCTET_MAX = 10  # discover 10.0.0.1..10.0.0.10
    VIP_COOLING_PERIOD = 60          # seconds before reclaimed VIP can be reassigned
    VIP_REUSE_COOLDOWN = 5           # avoid re-using a VIP immediately after release

    INITIAL_ASSIGN_ON_DISCOVERY = True
    AUTO_TOPUP_IN_HOUSEKEEPING = True

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
        self.vip_idle_since: Dict[str, float] = {}
        self.vip_ever_active: Dict[str, float] = {}
        self.vip_reclaimed_at: Dict[str, float] = {}
        self.vip_recently_used: Dict[str, float] = {}
        self.vip_active_sessions: Dict[str, Set[SessionKey]] = {}

        # reply VIP binding (legacy logging expectations)
        self.reply_vip_pair: Dict[Tuple[str, str, int], str] = {}
        self._reply_vip_by_5tuple: Dict[Tuple[str, str, int, int, int], str] = {}

        # VIP resource pool
        self.Resources: List[str] = self._generate_vips("10.0.0.9", self.NUM_VIPS)

        # sessions: session_table[key] -> SessionRecord
        self.session_table: Dict[SessionKey, SessionRecord] = {}

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
        self.vip_idle_since.pop(vip, None)
        if vip not in self.vip_ever_active:
            self.vip_ever_active[vip] = ts

    def _start_idle_timer(self, vip: str, ts: float, why: str) -> None:
        if vip not in self.vip_idle_since:
            self.vip_idle_since[vip] = ts
            self.logger.info("IDLE: %s idle start (reason: %s)", vip, why)

    def _mark_vip_reuse(self, vip: str, ts: float) -> None:
        if vip:
            self.vip_recently_used[vip] = ts

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
        self.logger.info("[SW] Switch %016x connected", dp.id)

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
                # Use longer timeout for ICMP sessions to avoid ping failures
                timeout = self.SESSION_NO_GROWTH_TIMEOUT * 2 if session.proto == 1 else self.SESSION_NO_GROWTH_TIMEOUT
                if age > timeout:
                    src_ip = session.src_ip_initial or session.key[0]
                    dst_ip = session.dst_ip_initial or session.key[1]
                    self.logger.info("SESSION: drop %s -> %s (%.1fs no growth)",
                                     src_ip, dst_ip, age)
                    self._finalize_session(session_key, now, reason="session drop")

        self.logger.info("STATS: polled %d sessions", total)

        # 2) mark idle VIPs based on last_seen timestamps
        for vip, owner in list(self.V2R_Mappings.items()):
            if vip in self.vip_idle_since:
                continue
            last = self.vip_last_seen.get(vip, self.vip_created_at.get(vip))
            if last is None:
                continue
            # Use longer timeout for ICMP VIPs to keep them available
            has_icmp_mapping = any(v == vip for v in self._reply_vip_by_5tuple.values()) or \
                              any(v == vip for v in self.reply_vip_pair.values())
            timeout = self.SESSION_NO_GROWTH_TIMEOUT * 4 if has_icmp_mapping else self.SESSION_NO_GROWTH_TIMEOUT
            if (now - last) > timeout and not self.vip_active_sessions.get(vip):
                self._start_idle_timer(vip, now, "housekeeping timeout")

        # 3) reclaim past grace
        for vip, owner in list(self.V2R_Mappings.items()):
            if vip not in self.vip_idle_since:
                continue
            # Don't reclaim VIPs that have ICMP reply mappings
            has_icmp_mapping = any(v == vip for v in self._reply_vip_by_5tuple.values()) or \
                              any(v == vip for v in self.reply_vip_pair.values())
            if has_icmp_mapping:
                self.logger.info("PROTECT: VIP %s protected from reclaim (has ICMP mappings)", vip)
                continue
            if (now - self.vip_idle_since[vip]) >= self.VIP_IDLE_TIMEOUT:
                self._reclaim_vip(vip)

        # 4) top-up immediately after reclaim
        if self.AUTO_TOPUP_IN_HOUSEKEEPING:
            for real_ip in list(self.detected_hosts):
                self._top_up_host(real_ip, now)

        # 5) proactive (light) discovery
        self._proactive_discovery(now)

        # 6) log cooling period status
        cooling_vips = [vip for vip, ts in self.vip_reclaimed_at.items()
                        if (now - ts) < self.VIP_COOLING_PERIOD]
        if cooling_vips:
            self.logger.info("COOLING: %d VIPs in cooling period: %s",
                             len(cooling_vips), sorted(cooling_vips)[:5])
            pass

        # 7) log snapshot
        self._log_vip_pools(now)

    def _top_up_host(self, real_ip: str, now: float) -> None:
        pool = self.host_vip_pools.setdefault(real_ip, set())
        assigned: List[str] = []
        while len(pool) < self.VIPS_PER_HOST and self.Resources:
            vip = self._take_resource_vip(now)
            if vip is None:
                break
            self._bind_vip_to_host(vip, real_ip, now)
            assigned.append(vip)
        if assigned:
            self.logger.info("TOPUP: host %s assigned %d VIP(s): %s",
                             real_ip, len(assigned), sorted(self.host_vip_pools.get(real_ip, set())))
            for vip in assigned:
                self._send_gratuitous_arp_to_all(vip)
                self._send_targeted_arp_updates(vip)

    def _take_resource_vip(self, now: float) -> Optional[str]:
        for idx, candidate in enumerate(self.Resources):
            if candidate in self.vip_reclaimed_at:
                if (now - self.vip_reclaimed_at[candidate]) < self.VIP_COOLING_PERIOD:
                    continue
            return self.Resources.pop(idx)
        return None

    def _bind_vip_to_host(self, vip: str, real_ip: str, now: float) -> None:
        self.vip_reclaimed_at.pop(vip, None)
        self.V2R_Mappings[vip] = real_ip
        self.host_vip_pools.setdefault(real_ip, set()).add(vip)
        self.vip_created_at[vip] = now
        self.vip_last_seen.pop(vip, None)
        self.vip_idle_since.pop(vip, None)
        self.vip_ever_active.pop(vip, None)
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
        self._purge_flows_for_vip(vip)

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
        self.logger.info("PACKET: %s -> %s (proto %d)", src_ip, dst_ip, proto)

        direction, session_key, client_real, server_real, client_port, server_port = \
            self._classify_flow(src_ip, dst_ip, proto, src_port, dst_port)

        session = self.session_table.get(session_key)
        new_session = False
        if not session:
            session = self._create_session_record(session_key, dp, now,
                                                   src_ip, dst_ip, proto)
            self.session_table[session_key] = session
            new_session = True
            # self.logger.info("SESSION: created %s -> %s (key=%s)", src_ip, dst_ip, session_key)
        # else:
            # self.logger.info("SESSION: reused %s -> %s (key=%s)", src_ip, dst_ip, session_key)

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
            if not session.vip_dst:
                session.vip_dst = vip_dst
            if not session.vip_locked:
                session.vip_locked = vip_dst
            self._touch_vip(vip_dst, now, "session create: vip_dst")
            self._register_reply_mapping(session, server_real, client_real,
                                         proto, vip_dst, client_port, server_port,
                                         icmp_pkt, tcp_pkt, udp_pkt)

        if direction == 'forward':
            vip_src = session.vip_src
            if not vip_src:
                vip_src = self._choose_outbound_vip(client_real, now)
                if not vip_src:
                    vip_src = self._allocate_vip_to_host(client_real, now, announce=True)
                session.vip_src = vip_src
                if vip_src:
                    self.vip_active_sessions.setdefault(vip_src, set()).add(session_key)
                    self._touch_vip(vip_src, now, "session create: vip_src")
                    self._mark_vip_reuse(vip_src, now)
                    self._send_targeted_arp_to_host_for_vip(vip_src, server_real)
            if session.vip_src:
                mac = self.vip_mac_map.get(session.vip_src) or self._generate_vip_mac(session.vip_src)
                self.vip_mac_map[session.vip_src] = mac
                actions.append(parser.OFPActionSetField(ipv4_src=session.vip_src))
                actions.append(parser.OFPActionSetField(eth_src=mac))
            if not forward_dst_mac:
                forward_dst_mac = self.host_ip_to_mac.get(server_real)
        else:  # reverse direction (server -> client)
            if proto == 1:
                # ICMP: always reply from the contacted VIP
                vip_src = session.vip_locked or session.vip_dst
                self.logger.info("REPLY OVERRIDE (ICMP): Using %s for %s->%s (client=%s)", 
                               vip_src, server_real, client_real, client_real)
            else:
                vip_src = session.vip_locked or self._select_reply_vip_5tuple(server_real, client_real,
                                                                             proto, client_port, server_port)
            if vip_src:
                session.vip_locked = vip_src
                self._touch_vip(vip_src, now, "reply packet")
                mac = self.vip_mac_map.get(vip_src) or self._generate_vip_mac(vip_src)
                self.vip_mac_map[vip_src] = mac
                actions.append(parser.OFPActionSetField(ipv4_src=vip_src))
                actions.append(parser.OFPActionSetField(eth_src=mac))
                self.vip_active_sessions.setdefault(vip_src, set()).add(session_key)
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
                         src_ip, dst_ip, proto, session.vip_dst, session_key)

        session.packet_count += 1
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
        
        # For ICMP, use original IPs in session key to distinguish between different VIPs
        if proto == 1:  # ICMP
            forward_key = (src_ip, dst_ip, proto, src_port, dst_port)
            reverse_key = (dst_ip, src_ip, proto, dst_port, src_port)
        else:
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

        # For ICMP, keep reply mappings persistent to avoid ping failures
        if session.proto != 1:  # Not ICMP
            for key in session.reply_keys:
                self._reply_vip_by_5tuple.pop(key, None)
            pair_key = (session.key[1], session.key[0], session.proto)
            if self.reply_vip_pair.get(pair_key) == session.vip_locked:
                self.reply_vip_pair.pop(pair_key, None)

        for vip in {session.vip_src, session.vip_locked, session.vip_dst}:
            if not vip:
                continue
            active = self.vip_active_sessions.get(vip)
            if active:
                active.discard(session_key)
                if not active:
                    self.vip_active_sessions.pop(vip, None)
                    # For ICMP, don't start idle timer immediately - keep VIP available
                    if session.proto != 1:
                        self._start_idle_timer(vip, ts, reason)
            else:
                # For ICMP, don't start idle timer immediately - keep VIP available
                if session.proto != 1:
                    self._start_idle_timer(vip, ts, reason)
            self._mark_vip_reuse(vip, ts)

    def _choose_outbound_vip(self, real_ip: str, now: float) -> Optional[str]:
        pool = self.host_vip_pools.get(real_ip, set())
        if not pool:
            return None
        icmp_vips: List[str] = []
        primary: List[str] = []
        cooling: List[str] = []
        fallback: List[str] = []
        for vip in pool:
            fallback.append(vip)
            # Prefer VIPs that have ICMP reply mappings (more likely to work)
            has_icmp_mapping = any(v == vip for v in self._reply_vip_by_5tuple.values()) or \
                              any(v == vip for v in self.reply_vip_pair.values())
            if has_icmp_mapping:
                icmp_vips.append(vip)
            if self.vip_active_sessions.get(vip):
                continue
            last_used = self.vip_recently_used.get(vip, 0.0)
            if (now - last_used) < self.VIP_REUSE_COOLDOWN:
                cooling.append(vip)
                continue
            primary.append(vip)
        # Prefer ICMP VIPs first, then primary, then cooling, then fallback
        if icmp_vips:
            return random.choice(icmp_vips)
        if primary:
            return random.choice(primary)
        if cooling:
            return random.choice(cooling)
        if fallback:
            return random.choice(fallback)
            return None

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
        if proto == 1:
            key = (server_real, client_real, 1, 0, 0)
        elif proto == 6:
            key = (server_real, client_real, 6, client_port, server_port)
        elif proto == 17:
            key = (server_real, client_real, 17, client_port, server_port)
        else:
            key = (server_real, client_real, proto, client_port, server_port)
        self._reply_vip_by_5tuple[key] = vip_dst
        session.reply_keys.add(key)
        self.logger.info("REPLY MAPPING: server=%s client=%s proto=%d uses VIP %s (5tuple key=%s)",
                         server_real, client_real, proto, vip_dst, key)
        # Force-lock ICMP replies to the contacted VIP
        if proto == 1 and session is not None:
            session.vip_locked = vip_dst

    # ---------------- VIP helpers ----------------
    def _allocate_vip_to_host(self, real_ip: str, now: float, announce: bool = True) -> Optional[str]:
        vip = self._take_resource_vip(now)
        if not vip:
            self.logger.warning("ALLOC: No non-cooling VIP resources available for host %s", real_ip)
            return None
        self._bind_vip_to_host(vip, real_ip, now)
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
                self.logger.warning("ARP: JIT failed - no MAC for host %s", target_real_ip)
                return
            
            # Send multiple times with small delays to ensure delivery
            for attempt in range(3):
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
                if attempt < 2:
                    hub.sleep(0.05)  # 50ms delay between attempts
            
            self.logger.info("ARP: targeted JIT for SNAT VIP %s -> host %s (MAC: %s, 3 attempts)", 
                           vip, target_real_ip, host_mac)
        except Exception as e:
            self.logger.warning("ARP: targeted JIT failed for %s->%s: %s", vip, target_real_ip, e)

    def _reclaim_vip(self, vip: str) -> None:
        real_ip = self.V2R_Mappings.pop(vip, None)
        if not real_ip:
            return
        pool = self.host_vip_pools.get(real_ip)
        if pool:
            pool.discard(vip)
        self.vip_created_at.pop(vip, None)
        self.vip_idle_since.pop(vip, None)
        self.vip_last_seen.pop(vip, None)
        self.vip_ever_active.pop(vip, None)
        self.vip_mac_map.pop(vip, None)
        self.vip_recently_used.pop(vip, None)
        self.vip_active_sessions.pop(vip, None)
        for k, v in list(self._reply_vip_by_5tuple.items()):
            if v == vip:
                self._reply_vip_by_5tuple.pop(k, None)
        for k, v in list(self.reply_vip_pair.items()):
            if v == vip:
                self.reply_vip_pair.pop(k, None)
        for session_key, session in list(self.session_table.items()):
            if session.vip_dst == vip or session.vip_src == vip or session.vip_locked == vip:
                self._finalize_session(session_key, time(), reason="vip reclaim")
        self._purge_flows_for_vip(vip)
        self.vip_reclaimed_at[vip] = time()
        if vip not in self.Resources:
            self.Resources.insert(0, vip)
        self.logger.info("RECLAIM: VIP %s reclaimed from %s (cooling period started)", vip, real_ip)

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
            while len(self.host_vip_pools[real_ip]) < self.VIPS_PER_HOST and self.Resources:
                vip = self._take_resource_vip(now)
                if vip is None:
                    break
                self._bind_vip_to_host(vip, real_ip, now)
                assigned.append(vip)
        self.logger.info("[+] New host %s (%s) - assigned %d VIPs", real_ip, mac, len(assigned))
        for vip in assigned:
            self._send_gratuitous_arp_to_all(vip)
            self._send_targeted_arp_updates(vip)

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
    def _select_reply_vip_5tuple(self, server_real, client_real, proto, sport, dport):
        if proto in (6, 17):
            key = (server_real, client_real, proto, dport, sport)
            vip = self._reply_vip_by_5tuple.get(key)
            if vip and self.V2R_Mappings.get(vip) == server_real:
                return vip
        elif proto == 1:
            key = (server_real, client_real, 1, 0, 0)
            vip = self._reply_vip_by_5tuple.get(key)
            if vip and self.V2R_Mappings.get(vip) == server_real:
                return vip
        return None

    # ---------------- logging ----------------
    def _log_vip_pools(self, now: float) -> None:
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
                # Host has no VIPs assigned
                continue
            self.logger.info("Host %s (%d VIPs):", real_ip, len(pool))
            self.logger.info(" %-13s %-9s %-8s %-10s %-12s", "VIP", "Uptime", "State", "Idle", "Reclaim")
            self.logger.info(" %-13s %-9s %-8s %-10s %-12s", "-------------", "---------", "--------", "----------", "----------")
            host_active = 0
            for vip in sorted(pool, key=ipkey):
                created = self.vip_created_at.get(vip, now)
                uptime = f"{max(0.0, (now - created)):.1f}s"
                last = self.vip_last_seen.get(vip)
                if (vip in self.vip_ever_active) and last is not None and (now - last) <= self.SESSION_NO_GROWTH_TIMEOUT:
                    state = "ACTIVE"
                    idle_str = "-"
                    recl_str = "-"
                    host_active += 1
                    active_total += 1
                else:
                    state = "IDLE"
                    if vip in self.vip_idle_since:
                        idle_for = now - self.vip_idle_since[vip]
                        idle_str = f"{idle_for:.1f}s"
                        recl_str = f"{max(0.0, self.VIP_IDLE_TIMEOUT - idle_for):.1f}s"
                    else:
                        idle_str = "0.0s"
                        recl_str = f"{float(self.VIP_IDLE_TIMEOUT):.1f}s"
                self.logger.info(" %-13s %-9s %-8s %-10s %-12s", vip, uptime, state, idle_str, recl_str)
                total += 1
            self.logger.info(" → %d active, %d idle", host_active, len(pool) - host_active)
        self.logger.info("=== SUMMARY: %d total VIPs (%d active, %d idle) ===",
                         total, active_total, total - active_total)
