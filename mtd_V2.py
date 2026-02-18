"""
Simplified Moving Target Defense Ryu controller.

Design goals:
- Simple time-based VIP rotation only.
- VIP state machine: PRIMARY -> GRACE -> RECLAIMED (time driven).
- No session table / refcount / stats growth logic.
- Straightforward flow installs visible in OVS:
  * ip,nw_dst=<vip> rewrite to real host
  * ip,nw_src=<real> rewrite to host VIP
- Keep table-miss to controller and ARP VIP replies.
"""

from time import time
from typing import Dict, List, Optional, Set

from ryu.base import app_manager
from ryu.controller import event, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, set_ev_cls
from ryu.lib import hub
from ryu.lib.packet import arp, ethernet, ipv4, packet
from ryu.ofproto import ofproto_v1_3


class EventMessage(event.EventBase):
    def __init__(self, message: str):
        super(EventMessage, self).__init__()
        self.msg = message


class MovingTargetDefense(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _EVENTS = [EventMessage]

    NUM_VIPS = 244
    HOUSEKEEPING_INTERVAL = 15
    ROTATE_INTERVAL = 60
    GRACE_PERIOD = 5
    DISCOVERY_RANGE_LAST_OCTET_MAX = 10
    VIP_POOL_START = "10.0.0.11"

    FLOW_PRIORITY_VIP = 100
    COOKIE_BASE = 0xA000_0000_0000_0000
    COOKIE_VIP_MASK = 0xFFFF_FFFF

    VIP_STATE_PRIMARY = "PRIMARY"
    VIP_STATE_GRACE = "GRACE"
    VIP_STATE_RECLAIMED = "RECLAIMED"

    def __init__(self, *args, **kwargs):
        super(MovingTargetDefense, self).__init__(*args, **kwargs)

        # Network topology tracking
        self.mac_to_port: Dict[int, Dict[str, int]] = {}  # dpid -> {mac: port}
        self.datapaths: Set["ryu.controller.controller.Datapath"] = set()  # Connected switches

        # Host discovery and mapping
        self.detected_hosts: Set[str] = set()  # discovered real host IPs (10.0.0.1-10.0.0.10)
        self.host_ip_to_mac: Dict[str, str] = {}  # Real host IP -> MAC
        self.host_mac_to_ip: Dict[str, str] = {}  # MAC -> Real host IP
        self.host_attachments: Dict[str, int] = {}  # Real host IP -> dpid

        # VIP assignment and state
        self.primary_vip: Dict[str, str] = {}  # Real host IP -> Primary VIP
        self.vip_owner: Dict[str, str] = {}  # VIP -> Real host IP
        self.vip_state: Dict[str, str] = {}  # VIP -> state
        self.vip_grace_until: Dict[str, float] = {}  # VIP -> grace expiry ts
        self.vip_mac_map: Dict[str, str] = {}  # VIP -> MAC
        self.vip_created_at: Dict[str, float] = {}  # VIP -> created ts
        self.host_vip_pools: Dict[str, Set[str]] = {}  # Real host IP -> VIP set

        # Active marker (best-effort)
        self.vip_active_sessions: Set[str] = set()

        # VIP resource pool
        self.Resources: List[str] = self._generate_vips(self.VIP_POOL_START, self.NUM_VIPS)

    # ---------------- lifecycle ----------------

    def start(self):
        super(MovingTargetDefense, self).start()
        self.threads.append(hub.spawn(self._ticker))
        self.threads.append(hub.spawn(self._rotation_loop))

    def _ticker(self):
        while True:
            self.send_event_to_observers(EventMessage("TICK"))
            hub.sleep(self.HOUSEKEEPING_INTERVAL)

    @set_ev_cls(EventMessage)
    def _housekeeping(self, ev):
        now = time()
        self._proactive_discovery(now)

        for vip, grace_until in list(self.vip_grace_until.items()):
            if now >= grace_until:
                self._reclaim_vip(vip)

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

    def _vip_cookie(self, vip: str) -> int:
        return self.COOKIE_BASE | (self._ip_to_int(vip) & self.COOKIE_VIP_MASK)

    def _add_flow(self, dp, priority, match, actions, table_id=0,
                  idle_timeout=0, hard_timeout=0, buffer_id=None, cookie=0):
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
            idle_timeout=idle_timeout,
            hard_timeout=hard_timeout,
            buffer_id=buffer_id,
        )
        dp.send_msg(mod)

    def _take_resource_vip(self) -> Optional[str]:
        if self.Resources:
            return self.Resources.pop(0)
        return None

    def _bind_primary_vip(self, host_ip: str, vip: str, now: float):
        self.primary_vip[host_ip] = vip
        self.vip_owner[vip] = host_ip
        self.vip_state[vip] = self.VIP_STATE_PRIMARY
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
        self.vip_created_at[vip] = now
        self.host_vip_pools.setdefault(host_ip, set()).add(vip)
        self.logger.info("BIND: host=%s vip=%s", host_ip, vip)

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

    # ---------------- rotation ----------------

    def _rotation_loop(self):
        while True:
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
                    self.vip_state[old_vip] = self.VIP_STATE_GRACE
                    self.vip_grace_until[old_vip] = now + self.GRACE_PERIOD
                    self.logger.info("ROTATE: host=%s new=%s old=%s -> GRACE",
                                     host_ip, new_vip, old_vip)

    # ---------------- host discovery ----------------

    def _learn_host(self, pkt, dpid: int):
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

        try:
            if not real_ip.startswith("10.0.0."):
                return
            last = int(real_ip.split(".")[-1])
            if last < 1 or last > self.DISCOVERY_RANGE_LAST_OCTET_MAX:
                return
        except Exception:
            return

        if mac:
            self.host_ip_to_mac[real_ip] = mac
            self.host_mac_to_ip[mac] = real_ip
        self.host_attachments[real_ip] = dpid

        if real_ip not in self.detected_hosts:
            self.detected_hosts.add(real_ip)
            self.host_vip_pools.setdefault(real_ip, set())

            now = time()
            new_vip = self._take_resource_vip()
            if new_vip:
                self._bind_primary_vip(real_ip, new_vip, now)
                self.logger.info("[+] New host %s (%s) - assigned VIP: %s",
                                 real_ip, mac, new_vip)

    def _send_arp_reply(self, dp, dst_mac, src_mac, src_ip, target_ip, out_port):
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
        if not self.datapaths:
            return

        if not hasattr(self, '_last_discovery'):
            self._last_discovery = {}

        for last_octet in range(1, self.DISCOVERY_RANGE_LAST_OCTET_MAX + 1):
            target_ip = f"10.0.0.{last_octet}"

            if target_ip in self.detected_hosts:
                continue

            if target_ip in self._last_discovery and (now - self._last_discovery[target_ip] < 60):
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
                        src='00:00:00:00:00:00'
                    ))
                    p.add_protocol(arp.arp(
                        opcode=arp.ARP_REQUEST,
                        src_mac='00:00:00:00:00:00',
                        src_ip='10.0.0.254',
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

    # ---------------- logging ----------------

    def _log_vip_pools(self, now: float):
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
                is_active = vip in self.vip_active_sessions
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

    # ---------------- flow removal tracking ----------------

    @set_ev_cls(ofp_event.EventOFPFlowRemoved, MAIN_DISPATCHER)
    def _flow_removed_handler(self, ev):
        msg = ev.msg
        cookie = msg.cookie

        if (cookie & ~self.COOKIE_VIP_MASK) == self.COOKIE_BASE:
            for vip in list(self.vip_active_sessions):
                if self._vip_cookie(vip) == cookie:
                    self.vip_active_sessions.discard(vip)
                    break

    # ---------------- VIP reclamation ----------------

    def _reclaim_vip(self, vip: str):
        owner = self.vip_owner.pop(vip, None)
        if not owner:
            return

        if owner in self.host_vip_pools:
            self.host_vip_pools[owner].discard(vip)

        self.vip_state.pop(vip, None)
        self.vip_grace_until.pop(vip, None)
        self.vip_mac_map.pop(vip, None)
        self.vip_created_at.pop(vip, None)
        self.vip_active_sessions.discard(vip)

        if self.primary_vip.get(owner) == vip:
            self.primary_vip.pop(owner, None)

        if vip not in self.Resources:
            self.Resources.append(vip)

        self.logger.info("RECLAIM: VIP %s from host %s", vip, owner)

    # ---------------- packet handling ----------------

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in(self, ev):
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

        # ARP
        arp_pkt = pkt.get_protocol(arp.arp)
        if arp_pkt:
            self._learn_host(pkt, dpid)
            self._handle_arp(msg, dp, pkt, arp_pkt, eth, in_port, dpid)
            return

        # IPv4
        ip4 = pkt.get_protocol(ipv4.ipv4)
        if not ip4:
            return

        self._learn_host(pkt, dpid)
        src_ip, dst_ip = ip4.src, ip4.dst

        src_is_real = src_ip in self.detected_hosts
        dst_is_real = dst_ip in self.detected_hosts
        src_is_vip = src_ip in self.vip_owner
        dst_is_vip = dst_ip in self.vip_owner

        if src_is_real and dst_is_real:
            self._handle_real_to_real(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
            return

        if src_is_real and dst_is_vip:
            self._handle_real_to_vip(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
            return

        if src_is_vip and dst_is_real:
            self._handle_vip_to_real(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
            return

        if src_is_vip and dst_is_vip:
            self._handle_vip_to_vip(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
            return

        self._forward_packet(msg, dp, in_port, dpid, eth.dst, ofp.OFPP_FLOOD)

    def _handle_arp(self, msg, dp, pkt, arp_pkt, eth, in_port, dpid):
        """Handle ARP packets.

        Key behavior:
        - If ARP is for a VIP: reply with VIP IP + VIP MAC (normal).
        - If ARP is for a REAL host IP: reply with REAL IP as sender IP,
          but use that host's PRIMARY VIP MAC as the sender MAC.
          This makes hosts accept the ARP answer for the REAL IP, while L2 uses VIP MAC.
        """
        if arp_pkt.opcode != arp.ARP_REQUEST:
            return

        target_ip = arp_pkt.dst_ip

        # 1) ARP for VIP (normal)
        if target_ip in self.vip_owner:
            vip_mac = self.vip_mac_map.get(target_ip)
            if vip_mac:
                self._send_arp_reply(dp, eth.src, vip_mac, target_ip, arp_pkt.src_ip, in_port)
            return

        # 2) ARP for REAL host IP (IMPORTANT FIX)
        if target_ip in self.detected_hosts:
            primary_vip = self.primary_vip.get(target_ip)
            if primary_vip:
                vip_mac = self.vip_mac_map.get(primary_vip)
                if vip_mac:
                    # Sender IP MUST be the real IP being asked about (target_ip)
                    self._send_arp_reply(dp, eth.src, vip_mac, target_ip, arp_pkt.src_ip, in_port)
            return

    def _handle_real_to_real(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_real, dst_real):
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        src_vip = self.primary_vip.get(src_real)
        dst_vip = self.primary_vip.get(dst_real)
        if not src_vip or not dst_vip:
            self.logger.warning("REAL-TO-REAL: Missing VIP for src=%s or dst=%s", src_real, dst_real)
            return

        src_vip_mac = self.vip_mac_map.get(src_vip)
        dst_real_mac = self.host_ip_to_mac.get(dst_real)
        if not src_vip_mac or not dst_real_mac:
            self.logger.warning("REAL-TO-REAL: Missing MAC for translation")
            return

        out_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)

        # Forward: h1(real)->h2(real) becomes src_vip -> dst_real (so h2 accepts)
        match = parser.OFPMatch(eth_type=0x0800, ipv4_src=src_real, ipv4_dst=dst_real)
        actions = [
            parser.OFPActionSetField(ipv4_src=src_vip),
            parser.OFPActionSetField(ipv4_dst=dst_real),
            parser.OFPActionSetField(eth_src=src_vip_mac),
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(out_port),
        ]
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                       cookie=self._vip_cookie(src_vip), idle_timeout=60)
        self.vip_active_sessions.add(src_vip)
        self.vip_active_sessions.add(dst_vip)

        # Reverse: h2(real)->h1(vip) or h1(real) situations
        src_real_mac = self.host_ip_to_mac.get(src_real)
        dst_vip_mac = self.vip_mac_map.get(dst_vip)
        if src_real_mac and dst_vip_mac:
            out_port_back = self.mac_to_port.get(dpid, {}).get(src_real_mac, ofp.OFPP_FLOOD)

            # Case A: h2 replies to h1 REAL directly (dst=src_real)
            match_rev = parser.OFPMatch(eth_type=0x0800, ipv4_src=dst_real, ipv4_dst=src_real)
            actions_rev = [
                parser.OFPActionSetField(ipv4_src=dst_vip),
                parser.OFPActionSetField(ipv4_dst=src_real),
                parser.OFPActionSetField(eth_src=dst_vip_mac),
                parser.OFPActionSetField(eth_dst=src_real_mac),
                parser.OFPActionOutput(out_port_back),
            ]
            self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match_rev, actions=actions_rev,
                           cookie=self._vip_cookie(dst_vip), idle_timeout=60)
            self.vip_active_sessions.add(src_vip)
            self.vip_active_sessions.add(dst_vip)

            # Case B: h2 replies to h1 VIP (dst=src_vip)
            match_vip_reply = parser.OFPMatch(eth_type=0x0800, ipv4_src=dst_real, ipv4_dst=src_vip)
            actions_vip_reply = [
                parser.OFPActionSetField(ipv4_src=dst_vip),
                parser.OFPActionSetField(ipv4_dst=src_real),
                parser.OFPActionSetField(eth_src=dst_vip_mac),
                parser.OFPActionSetField(eth_dst=src_real_mac),
                parser.OFPActionOutput(out_port_back),
            ]
            self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match_vip_reply, actions=actions_vip_reply,
                           cookie=self._vip_cookie(dst_vip), idle_timeout=60)
            self.vip_active_sessions.add(src_vip)
            self.vip_active_sessions.add(dst_vip)

        self._send_packet_out(msg, dp, in_port, actions)

    def _handle_real_to_vip(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_real, dst_vip):
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        src_vip = self.primary_vip.get(src_real)
        if not src_vip:
            return

        real_dst = self.vip_owner.get(dst_vip)
        if not real_dst:
            return

        src_vip_mac = self.vip_mac_map.get(src_vip)
        dst_real_mac = self.host_ip_to_mac.get(real_dst)
        dst_vip_mac = self.vip_mac_map.get(dst_vip)
        if not src_vip_mac or not dst_real_mac or not dst_vip_mac:
            return

        out_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)

        match = parser.OFPMatch(eth_type=0x0800, ipv4_src=src_real, ipv4_dst=dst_vip)
        actions = [
            parser.OFPActionSetField(ipv4_src=src_vip),
            parser.OFPActionSetField(ipv4_dst=real_dst),
            parser.OFPActionSetField(eth_src=src_vip_mac),
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(out_port),
        ]
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                       cookie=self._vip_cookie(src_vip), idle_timeout=60)
        self.vip_active_sessions.add(src_vip)
        self.vip_active_sessions.add(dst_vip)

        src_real_mac = self.host_ip_to_mac.get(src_real)
        if src_real_mac:
            out_port_back = self.mac_to_port.get(dpid, {}).get(src_real_mac, ofp.OFPP_FLOOD)
            match_rev = parser.OFPMatch(eth_type=0x0800, ipv4_src=real_dst, ipv4_dst=src_vip)
            actions_rev = [
                parser.OFPActionSetField(ipv4_src=dst_vip),
                parser.OFPActionSetField(ipv4_dst=src_real),
                parser.OFPActionSetField(eth_src=dst_vip_mac),
                parser.OFPActionSetField(eth_dst=src_real_mac),
                parser.OFPActionOutput(out_port_back),
            ]
            self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match_rev, actions=actions_rev,
                           cookie=self._vip_cookie(dst_vip), idle_timeout=60)
            self.vip_active_sessions.add(src_vip)
            self.vip_active_sessions.add(dst_vip)

        self._send_packet_out(msg, dp, in_port, actions)

    def _handle_vip_to_real(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_vip, dst_real):
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        real_src = self.vip_owner.get(src_vip)
        if not real_src:
            return

        dst_real_mac = self.host_ip_to_mac.get(dst_real)
        if not dst_real_mac:
            return

        out_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)

        match = parser.OFPMatch(eth_type=0x0800, ipv4_src=src_vip, ipv4_dst=dst_real)
        actions = [
            parser.OFPActionSetField(ipv4_src=real_src),
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(out_port),
        ]
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                       cookie=self._vip_cookie(src_vip), idle_timeout=60)
        self.vip_active_sessions.add(src_vip)

        # Reverse: dst_real -> real_src becomes dst_real -> src_vip
        src_real_mac = self.host_ip_to_mac.get(real_src)
        if src_real_mac:
            out_port_back = self.mac_to_port.get(dpid, {}).get(src_real_mac, ofp.OFPP_FLOOD)
            match_rev = parser.OFPMatch(eth_type=0x0800, ipv4_src=dst_real, ipv4_dst=real_src)

            # IMPORTANT FIX: eth_dst should be real host MAC (src_real_mac), not VIP MAC
            actions_rev = [
                parser.OFPActionSetField(ipv4_dst=src_vip),
                parser.OFPActionSetField(eth_dst=src_real_mac),
                parser.OFPActionOutput(out_port_back),
            ]
            self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match_rev, actions=actions_rev,
                           cookie=self._vip_cookie(src_vip), idle_timeout=60)
            self.vip_active_sessions.add(src_vip)

        self._send_packet_out(msg, dp, in_port, actions)

    def _handle_vip_to_vip(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_vip, dst_vip):
        parser = dp.ofproto_parser
        ofp = dp.ofproto

        real_dst = self.vip_owner.get(dst_vip)
        if not real_dst:
            return

        dst_real_mac = self.host_ip_to_mac.get(real_dst)
        if not dst_real_mac:
            return

        out_port = self.mac_to_port.get(dpid, {}).get(dst_real_mac, ofp.OFPP_FLOOD)

        match = parser.OFPMatch(eth_type=0x0800, ipv4_src=src_vip, ipv4_dst=dst_vip)
        actions = [
            parser.OFPActionSetField(ipv4_dst=real_dst),
            parser.OFPActionSetField(eth_dst=dst_real_mac),
            parser.OFPActionOutput(out_port),
        ]
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                       cookie=self._vip_cookie(dst_vip), idle_timeout=60)
        self.vip_active_sessions.add(dst_vip)

        self._send_packet_out(msg, dp, in_port, actions)

    def _forward_packet(self, msg, dp, in_port, dpid, dst_mac, out_port):
        parser = dp.ofproto_parser
        actions = [parser.OFPActionOutput(out_port)]
        self._send_packet_out(msg, dp, in_port, actions)

    def _send_packet_out(self, msg, dp, in_port, actions):
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
