

"""
DNS-based Moving Target Defense Ryu controller.

Design:
- Hosts resolve hostnames to VIPs via DNS (handled by external DNS server)
- VIPs are assigned to hosts and rotate periodically
- No SNAT/DNAT - hosts communicate directly using VIPs
- Simple forwarding rules - VIPs are just regular IPs
- VIP rotation: DNS TTL expires, clients get new VIP on next lookup
- Much simpler than SNAT/DNAT approach
"""

import socket
from time import time
from typing import Dict, List, Optional, Set

from ryu.base import app_manager
from ryu.controller import event, ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, set_ev_cls
from ryu.lib import hub
from ryu.lib.packet import arp, ethernet, icmp, ipv4, packet, tcp, udp
from ryu.ofproto import ofproto_v1_3


class EventMessage(event.EventBase):
    def __init__(self, message: str):
        super(EventMessage, self).__init__()


class MovingTargetDefenseDNS(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _EVENTS = [EventMessage]

    NUM_VIPS = 244
    HOUSEKEEPING_INTERVAL = 15
    ROTATE_INTERVAL = 60
    # GRACE VIPs: If idle when moved to GRACE (flow_refs = 0), reclaim immediately (return to pool)
    #             If active when moved to GRACE (flow_refs > 0), keep until flows end
    DISCOVERY_RANGE_LAST_OCTET_MAX = 10
    VIP_POOL_START = "10.0.0.11"

    FLOW_PRIORITY_VIP = 100
    COOKIE_BASE = 0xA000_0000_0000_0000
    COOKIE_VIP_MASK = 0xFFFF_FFFF
    CONTROLLER_DISCOVERY_MAC = "02:00:00:00:00:fe"

    VIP_STATE_PRIMARY = "PRIMARY"
    VIP_STATE_GRACE = "GRACE"

    def __init__(self, *args, **kwargs):
        super(MovingTargetDefenseDNS, self).__init__(*args, **kwargs)

        # Network topology tracking
        self.mac_to_port: Dict[int, Dict[str, int]] = {}  # dpid -> {mac: port}
        self.datapaths: Set["ryu.controller.controller.Datapath"] = set()
        
        # Host discovery and mapping
        self.detected_hosts: Set[str] = set()  # Set of discovered real host IPs (10.0.0.1-10.0.0.10)
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
        
        # VIP resource pool
        self.Resources: List[str] = self._generate_vips(self.VIP_POOL_START, self.NUM_VIPS)

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
        
        # Handle VIPs in GRACE state
        # Use flow_refs to determine activity: if flow_refs > 0, VIP is active; if flow_refs = 0, VIP is idle
        # IMPORTANT: Only process GRACE VIPs - PRIMARY VIPs should never be reclaimed
        for vip in list(self.vip_state.keys()):
            if self.vip_state.get(vip) != self.VIP_STATE_GRACE:
                continue
            
            flow_refs = self.vip_flow_refs.get(vip, 0)
            
            if flow_refs <= 0:
                # No active flows = VIP is idle - reclaim immediately (return to pool)
                self.logger.info("RECLAIM: VIP %s is idle (no active flows), reclaiming immediately", vip)
                self._delete_flows_by_cookie(vip)
                self._reclaim_vip(vip)
            else:
                # VIP has active flows - keep in GRACE until flows end
                self.logger.debug("GRACE: VIP %s still active (%d flow refs), keeping", vip, flow_refs)
        
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
            self.logger.debug("FLOW_ADD: VIP %s flow installed (refs: %d -> %d)", vip, old_refs, old_refs + 1)

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
        
        self.logger.debug("FLOW_REMOVED: VIP %s flow expired (refs: %d -> %d, state=%s)", 
                         vip, old_refs, new_refs, self.vip_state.get(vip, "UNKNOWN"))
        
        # If GRACE VIP has no flows left, reclaim immediately
        if self.vip_state.get(vip) == self.VIP_STATE_GRACE and new_refs == 0:
            self.logger.info("FLOW_REMOVED: VIP %s (GRACE) all flows expired, reclaiming immediately", vip)
            self._delete_flows_by_cookie(vip)
            self._reclaim_vip(vip)

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
        self.vip_created_at[vip] = now
        self.host_vip_pools.setdefault(host_ip, set()).add(vip)
        self.logger.info("BIND: host=%s vip=%s", host_ip, vip)
        # Update DNS mapping file
        self._update_dns_mapping()

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
                    # Check if VIP is idle or active using flow_refs
                    flow_refs = self.vip_flow_refs.get(old_vip, 0)
                    if flow_refs <= 0:
                        # No active flows = VIP is idle - reclaim immediately
                        self.logger.info("ROTATE: host=%s new=%s old=%s -> GRACE (idle, no flows), reclaiming immediately",
                                         host_ip, new_vip, old_vip)
                        self._delete_flows_by_cookie(old_vip)
                        self._reclaim_vip(old_vip)
                    else:
                        # VIP has active flows - keep in GRACE until flows end
                        self.logger.info("ROTATE: host=%s new=%s old=%s -> GRACE (active, %d flows), will reclaim when flows end",
                                         host_ip, new_vip, old_vip, flow_refs)

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

        # Only learn hosts in discovery range
        try:
            if not real_ip.startswith("10.0.0."):
                return
            last = int(real_ip.split(".")[-1])
            if last < 1 or last > self.DISCOVERY_RANGE_LAST_OCTET_MAX:
                return
        except Exception:
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

        for last_octet in range(1, self.DISCOVERY_RANGE_LAST_OCTET_MAX + 1):
            target_ip = f"10.0.0.{last_octet}"

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
                
                # Mark as ACTIVE if VIP has active flows (flow_refs > 0)
                flow_refs = self.vip_flow_refs.get(vip, 0)
                is_active = flow_refs > 0
                
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
        """Reclaim a VIP and return it to the resource pool."""
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

        if self.primary_vip.get(owner) == vip:
            self.primary_vip.pop(owner, None)

        if vip not in self.Resources:
            self.Resources.append(vip)

        self.logger.info("RECLAIM: VIP %s from host %s", vip, owner)
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
            self._handle_real_to_vip(msg, dp, pkt, ip4, eth, in_port, dpid, src_ip, dst_ip)
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
        cookie = self._vip_cookie(src_vip)
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
            cookie_rev = self._vip_cookie(dst_vip)
            self.logger.debug("REAL-TO-REAL: Installing reverse flow for dst_vip=%s (cookie=0x%016x) to track flow_refs", 
                             dst_vip, cookie_rev)
            self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match_rev, actions=actions_rev,
                          cookie=cookie_rev, idle_timeout=5)

        self.logger.debug("REAL-TO-REAL: %s -> %s (translated to %s -> %s)", 
                         src_real, dst_real, src_vip, dst_real)

    def _handle_real_to_vip(self, msg, dp, pkt, ip4, eth, in_port, dpid, src_real, dst_vip):
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
        cookie = self._vip_cookie(src_vip)
        # Install flow for subsequent packets
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                      cookie=cookie, idle_timeout=5)
        self.logger.debug("REAL-TO-VIP: Installed forward flow for TCP/UDP: %s -> %s (VIP: %s -> %s)", 
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
            cookie_rev = self._vip_cookie(dst_vip)
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

        # Reverse SNAT: VIP → real
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
        cookie = self._vip_cookie(src_vip)
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
        cookie = self._vip_cookie(dst_vip)
        self._add_flow(dp, priority=self.FLOW_PRIORITY_VIP, match=match, actions=actions,
                      cookie=cookie, idle_timeout=5)

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
