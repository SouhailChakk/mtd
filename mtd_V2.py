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
        self.primary_vip: Dict[str, str] = {}
        self.vip_owner: Dict[str, str] = {}
        self.vip_state: Dict[str, str] = {}
        self.vip_grace_until: Dict[str, float] = {}
        self.vip_mac_map: Dict[str, str] = {}

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

    def _add_flow(self, dp, priority, match, actions, table_id=0, idle_timeout=0, hard_timeout=0, buffer_id=None, cookie=0):
        """Install a flow rule on the switch."""
        parser = dp.ofproto_parser
        ofp = dp.ofproto
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
        """Take a VIP from the resource pool."""
        if self.Resources:
            return self.Resources.pop(0)
        return None

    def _bind_primary_vip(self, host_ip: str, vip: str, now: float):
        """Bind a VIP as the primary VIP for a host."""
        self.primary_vip[host_ip] = vip
        self.vip_owner[vip] = host_ip
        self.vip_state[vip] = self.VIP_STATE_PRIMARY
        self.vip_mac_map[vip] = self._generate_vip_mac(vip)
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

        ip4 = pkt.get_protocol(ipv4.ipv4)
        if not ip4:
            return

        src_ip, dst_ip = ip4.src, ip4.dst

        actions = []
        out_port = ofp.OFPP_FLOOD

        if dst_ip in self.vip_owner:
            real_dst = self.vip_owner[dst_ip]
            dst_mac = self.host_ip_to_mac.get(real_dst)
            actions.append(parser.OFPActionSetField(ipv4_dst=real_dst))
            if dst_mac:
                actions.append(parser.OFPActionSetField(eth_dst=dst_mac))
                out_port = self.mac_to_port.get(dpid, {}).get(dst_mac, ofp.OFPP_FLOOD)

        actions.append(parser.OFPActionOutput(out_port))

        data = msg.data if msg.buffer_id == ofp.OFP_NO_BUFFER else None
        out = parser.OFPPacketOut(
            datapath=dp,
            buffer_id=msg.buffer_id,
            in_port=in_port,
            actions=actions,
            data=data,
        )
        dp.send_msg(out)
