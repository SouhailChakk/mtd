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

from collections import defaultdict
from time import time
from typing import Dict, List, Optional, Set, Tuple

from ryu.base import app_manager
from ryu.controller import event, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, set_ev_cls
from ryu.lib import hub
from ryu.lib.packet import arp, ethernet, ipv4, packet, tcp, udp
from ryu.ofproto import ofproto_v1_3


class EventMessage(event.EventBase):
    def __init__(self, message: str):
        super(EventMessage, self).__init__()
        self.msg = message


class MovingTargetDefense(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _EVENTS = [EventMessage]

    NUM_VIPS = 244
    HOUSEKEEPING_INTERVAL = 2
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

        self.mac_to_port: Dict[int, Dict[str, int]] = {}
        self.datapaths: Set["ryu.controller.controller.Datapath"] = set()

        self.detected_hosts: Set[str] = set()
        self.host_ip_to_mac: Dict[str, str] = {}
        self.host_mac_to_ip: Dict[str, str] = {}

        self.primary_vip: Dict[str, str] = {}
        self.vip_owner: Dict[str, str] = {}
        self.host_vips: Dict[str, Set[str]] = defaultdict(set)
        self.vip_state: Dict[str, str] = {}
        self.vip_grace_until: Dict[str, float] = {}
        self.vip_mac_map: Dict[str, str] = {}

        self.Resources: List[str] = self._generate_vips(self.VIP_POOL_START, self.NUM_VIPS)

    def start(self):
        super(MovingTargetDefense, self).start()
        self.threads.append(hub.spawn(self._ticker))
        self.threads.append(hub.spawn(self._rotation_loop))

    def _ticker(self):
        while True:
            self.send_event_to_observers(EventMessage("TICK"))
            hub.sleep(self.HOUSEKEEPING_INTERVAL)

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

    def _set_vip_state(self, vip: str, state: str, now: float, reason: str):
        old = self.vip_state.get(vip)
        self.vip_state[vip] = state
        if state == self.VIP_STATE_GRACE:
            self.vip_grace_until[vip] = now + self.GRACE_PERIOD
        else:
            self.vip_grace_until.pop(vip, None)
        self.logger.info("VIP STATE: %s %s -> %s (%s)", vip, old or "<new>", state, reason)

    def _take_resource_vip(self) -> Optional[str]:
        if not self.Resources:
            return None
        return self.Resources.pop(0)

    def _bind_primary_vip(self, host_ip: str, vip: str, now: float):
        self.vip_owner[vip] = host_ip
        self.primary_vip[host_ip] = vip
        self.host_vips[host_ip].add(vip)
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
        self._set_vip_state(vip, self.VIP_STATE_PRIMARY, now, "bind primary")

    def _build_ip_match(self, parser, in_port: int, src_ip: str, dst_ip: str,
                        proto: int, src_port: int, dst_port: int):
        match_kwargs = {
            "in_port": in_port,
            "eth_type": 0x0800,
            "ipv4_src": src_ip,
            "ipv4_dst": dst_ip,
            "ip_proto": proto,
        }
        if proto == 6:
            match_kwargs.update(tcp_src=src_port, tcp_dst=dst_port)
        elif proto == 17:
            match_kwargs.update(udp_src=src_port, udp_dst=dst_port)
        return parser.OFPMatch(**match_kwargs)

    def _add_flow(self, dp, priority, match, actions, cookie=0, table_id=0,
                  hard_timeout=0, idle_timeout=30):
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        inst = [parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions)]
        mod = parser.OFPFlowMod(
            datapath=dp,
            table_id=table_id,
            priority=priority,
            cookie=cookie,
            cookie_mask=0,
            match=match,
            instructions=inst,
            hard_timeout=hard_timeout,
            idle_timeout=idle_timeout,
        )
        self.logger.info(
            "FLOW ADD: dp=%016x table=%d prio=%d cookie=0x%016x match=%s actions=%s idle=%d hard=%d",
            dp.id, table_id, priority, cookie, match, actions, idle_timeout, hard_timeout,
        )
        dp.send_msg(mod)

    def _delete_flow(self, dp, match=None, cookie=0, cookie_mask=0, table_id=None, strict=False):
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        cmd = ofp.OFPFC_DELETE_STRICT if strict else ofp.OFPFC_DELETE
        if table_id is None:
            table_id = ofp.OFPTT_ALL
        if match is None:
            match = parser.OFPMatch()
        mod = parser.OFPFlowMod(
            datapath=dp,
            table_id=table_id,
            command=cmd,
            out_port=ofp.OFPP_ANY,
            out_group=ofp.OFPG_ANY,
            cookie=cookie,
            cookie_mask=cookie_mask,
            match=match,
        )
        self.logger.info(
            "FLOW DEL: dp=%016x table=%s cmd=%s cookie=0x%016x mask=0x%016x match=%s out_port=ANY out_group=ANY",
            dp.id,
            "ALL" if table_id == ofp.OFPTT_ALL else table_id,
            "DELETE_STRICT" if strict else "DELETE",
            cookie,
            cookie_mask,
            match,
        )
        dp.send_msg(mod)

    def _purge_flows_for_vip(self, vip: str):
        cookie = self._vip_cookie(vip)
        for dp in list(self.datapaths):
            parser = dp.ofproto_parser
            self._delete_flow(dp, cookie=cookie, cookie_mask=0xFFFF_FFFF_FFFF_FFFF, table_id=dp.ofproto.OFPTT_ALL)
            self._delete_flow(dp, match=parser.OFPMatch(eth_type=0x0800, ipv4_dst=vip), table_id=dp.ofproto.OFPTT_ALL)
            self._delete_flow(dp, match=parser.OFPMatch(eth_type=0x0800, ipv4_src=vip), table_id=dp.ofproto.OFPTT_ALL)
        self.logger.info("FLOW: purged VIP %s using cookie+match deletes", vip)

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

    @set_ev_cls(EventMessage)
    def _housekeeping(self, _):
        now = time()
        for vip, state in list(self.vip_state.items()):
            if state != self.VIP_STATE_GRACE:
                continue
            grace_until = self.vip_grace_until.get(vip, 0.0)
            if now >= grace_until:
                self.logger.info("RECLAIM CHECK: vip=%s state=GRACE now=%.3f grace_until=%.3f -> reclaim", vip, now, grace_until)
                self._reclaim_vip(vip, now, "grace timeout")
            else:
                self.logger.info("RECLAIM CHECK: vip=%s state=GRACE now=%.3f grace_until=%.3f -> keep", vip, now, grace_until)

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
                self._send_gratuitous_arp_to_all(new_vip)
                self._send_targeted_arp_updates(new_vip)
                if old_vip and old_vip != new_vip:
                    self._set_vip_state(old_vip, self.VIP_STATE_GRACE, now, f"rotation {host_ip}")
                    self.logger.info("ROTATE: host=%s new_primary=%s old=%s -> GRACE", host_ip, new_vip, old_vip)

    def _reclaim_vip(self, vip: str, now: float, reason: str):
        owner = self.vip_owner.pop(vip, None)
        if not owner:
            return
        if self.primary_vip.get(owner) == vip:
            self.primary_vip.pop(owner, None)
        self.host_vips[owner].discard(vip)
        self._set_vip_state(vip, self.VIP_STATE_RECLAIMED, now, reason)
        self._purge_flows_for_vip(vip)
        self.vip_state.pop(vip, None)
        self.vip_grace_until.pop(vip, None)
        self.vip_mac_map.pop(vip, None)
        if vip not in self.Resources:
            self.Resources.append(vip)
        self.logger.info("RECLAIM: vip=%s owner=%s (%s)", vip, owner, reason)

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

        self._learn_host(pkt)

        a = pkt.get_protocol(arp.arp)
        if a and a.opcode == arp.ARP_REQUEST:
            self._handle_arp_request(dp, eth, a, in_port)
            return

        ip4 = pkt.get_protocol(ipv4.ipv4)
        if not ip4:
            return

        tcp_pkt = pkt.get_protocol(tcp.tcp)
        udp_pkt = pkt.get_protocol(udp.udp)

        src_ip, dst_ip, proto = ip4.src, ip4.dst, ip4.proto
        src_port = tcp_pkt.src_port if tcp_pkt else (udp_pkt.src_port if udp_pkt else 0)
        dst_port = tcp_pkt.dst_port if tcp_pkt else (udp_pkt.dst_port if udp_pkt else 0)

        src_real = self.vip_owner.get(src_ip, src_ip)
        dst_real = self.vip_owner.get(dst_ip, dst_ip)

        actions = []
        out_port = ofp.OFPP_FLOOD
        flow_cookie = 0

        # Forward: dst is VIP or known host -> rewrite to real destination
        vip_dst = None
        if dst_ip in self.vip_owner:
            vip_dst = dst_ip
            real_dst = self.vip_owner[dst_ip]
        elif dst_real in self.detected_hosts and dst_real in self.primary_vip:
            vip_dst = self.primary_vip[dst_real]
            real_dst = dst_real
        else:
            real_dst = dst_ip

        if vip_dst:
            flow_cookie = self._vip_cookie(vip_dst)
            dst_mac = self.host_ip_to_mac.get(real_dst)
            actions.append(parser.OFPActionSetField(ipv4_dst=real_dst))
            if dst_mac:
                actions.append(parser.OFPActionSetField(eth_dst=dst_mac))
                out_port = self.mac_to_port.get(dpid, {}).get(dst_mac, ofp.OFPP_FLOOD)

            # Reverse source rewrite: real source host -> current visible VIP
            if src_real in self.detected_hosts and src_real in self.primary_vip:
                vip_src = self.primary_vip[src_real]
                vip_src_mac = self.vip_mac_map.get(vip_src) or self._generate_vip_mac(vip_src)
                self.vip_mac_map[vip_src] = vip_src_mac
                actions.append(parser.OFPActionSetField(ipv4_src=vip_src))
                actions.append(parser.OFPActionSetField(eth_src=vip_src_mac))

        if not actions:
            actions.append(parser.OFPActionOutput(ofp.OFPP_FLOOD))
        else:
            actions.append(parser.OFPActionOutput(out_port))

            if out_port != ofp.OFPP_FLOOD and flow_cookie:
                match = self._build_ip_match(parser, in_port, src_ip, dst_ip, proto, src_port, dst_port)
                self._add_flow(dp,
                               priority=self.FLOW_PRIORITY_VIP,
                               match=match,
                               actions=actions[:-1],
                               table_id=0,
                               cookie=flow_cookie,
                               idle_timeout=30,
                               hard_timeout=0)

        data = msg.data if msg.buffer_id == ofp.OFP_NO_BUFFER else None
        out = parser.OFPPacketOut(
            datapath=dp,
            buffer_id=msg.buffer_id,
            in_port=in_port,
            actions=actions,
            data=data,
        )
        dp.send_msg(out)

    def _handle_arp_request(self, dp, eth, a, in_port):
        dip, sip, smac = a.dst_ip, a.src_ip, a.src_mac
        if dip in self.vip_owner:
            mac = self.vip_mac_map.get(dip) or self._generate_vip_mac(dip)
            self.vip_mac_map[dip] = mac
            self._send_arp_reply(dp, eth.ethertype, eth.src, mac, dip, smac, sip, in_port)
            self.logger.info("ARP: replied VIP %s -> %s", dip, mac)
            return
        if dip in self.host_ip_to_mac:
            mac = self.host_ip_to_mac[dip]
            self._send_arp_reply(dp, eth.ethertype, eth.src, mac, dip, smac, sip, in_port)
            self.logger.info("ARP: replied real %s -> %s", dip, mac)

    def _learn_host(self, pkt):
        eth_pkt = pkt.get_protocol(ethernet.ethernet)
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        if arp_pkt:
            real_ip, mac = arp_pkt.src_ip, arp_pkt.src_mac
        elif ip_pkt:
            real_ip, mac = ip_pkt.src, (eth_pkt.src if eth_pkt else None)
        else:
            return

        try:
            if not real_ip.startswith("10.0.0."):
                return
            last = int(real_ip.split(".")[-1])
            if last < 1 or last > self.DISCOVERY_RANGE_LAST_OCTET_MAX:
                return
        except Exception:
            return

        self.detected_hosts.add(real_ip)
        if mac:
            self.host_ip_to_mac[real_ip] = mac
            self.host_mac_to_ip[mac] = real_ip

        if real_ip not in self.primary_vip:
            now = time()
            vip = self._take_resource_vip()
            if not vip:
                self.logger.warning("DISCOVERY: no VIP available for %s", real_ip)
                return
            self._bind_primary_vip(real_ip, vip, now)
            self._send_gratuitous_arp_to_all(vip)
            self._send_targeted_arp_updates(vip)
            self.logger.info("DISCOVERY: host=%s mac=%s primary_vip=%s", real_ip, mac, vip)

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
            data=p.data,
        ))

    def _send_gratuitous_arp_to_all(self, vip: str):
        if not self.datapaths:
            return
        mac = self.vip_mac_map.get(vip) or self._generate_vip_mac(vip)
        self.vip_mac_map[vip] = mac
        for dp in list(self.datapaths):
            parser = dp.ofproto_parser
            ofp = dp.ofproto
            p = packet.Packet()
            p.add_protocol(ethernet.ethernet(ethertype=0x0806, dst='ff:ff:ff:ff:ff:ff', src=mac))
            p.add_protocol(arp.arp(opcode=arp.ARP_REPLY,
                                   src_mac=mac, src_ip=vip,
                                   dst_mac='ff:ff:ff:ff:ff:ff', dst_ip=vip))
            p.serialize()
            dp.send_msg(parser.OFPPacketOut(
                datapath=dp,
                buffer_id=ofp.OFP_NO_BUFFER,
                in_port=ofp.OFPP_CONTROLLER,
                actions=[parser.OFPActionOutput(ofp.OFPP_FLOOD)],
                data=p.data,
            ))
        self.logger.info("GARP: announced VIP %s", vip)

    def _send_targeted_arp_updates(self, vip: str):
        mac = self.vip_mac_map.get(vip) or self._generate_vip_mac(vip)
        for dp in list(self.datapaths):
            parser = dp.ofproto_parser
            ofp = dp.ofproto
            for host_ip, host_mac in list(self.host_ip_to_mac.items()):
                out_port = self.mac_to_port.get(dp.id, {}).get(host_mac, ofp.OFPP_FLOOD)
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
                    data=p.data,
                ))
        self.logger.info("ARP: targeted updates sent for VIP %s", vip)
