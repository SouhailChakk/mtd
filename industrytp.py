#!/usr/bin/env python
# -*- coding: utf-8 -*- 
# =============================================================================
# industrytp.py — Industry-realistic MTD topology
# Built on simpletp.py, scaled using real switch port counts
#
# Switch port sizes:
#   4-port  -> small  topology (~16  hosts, 13 switches)
#   24-port -> medium topology (~108 hosts, 11 switches)
#   48-port -> large  topology (~504 hosts, 23 switches)
#
# Architecture: 3-tier (Core -> Aggregation -> Edge -> Hosts)
#   Edge switches : ports//2 downlinks to hosts, ports//2 uplinks to agg
#   Agg  switches : ports//2 downlinks from edge, ports//2 uplinks to core
#   Core switches : one port per agg switch
#
# All hosts get flat sequential IPs on 10.0.0.x/24:
#   h1 -> 10.0.0.1, h2 -> 10.0.0.2 ... hN -> 10.0.0.N
#
# Real host range  : 10.0.0.1   - 10.0.0.128
# VIP range        : 10.0.0.129 - 10.0.0.253 then 10.0.1.x onward
# Controller probe : 10.0.0.254 (reserved, never a real host)
#
# Usage:
#   sudo python industrytp.py 4     # 4-port  switches (~16  hosts)
#   sudo python industrytp.py 24    # 24-port switches (~108 hosts)
#   sudo python industrytp.py 48    # 48-port switches (~504 hosts)
# =============================================================================

from mininet.topo import Topo
from mininet.net import Mininet
from mininet.node import OVSKernelSwitch, RemoteController
from mininet.cli import CLI
from mininet.log import setLogLevel
import sys
import math


# =============================================================================
# Topology parameters per port count
# =============================================================================

# Each entry: (hosts_per_edge, edges_per_agg)
# Derived from splitting ports 50/50 between downlinks and uplinks
SWITCH_CONFIGS = {
    4:  {'hosts_per_edge': 2,  'edges_per_agg': 2},   # half=2
    24: {'hosts_per_edge': 12, 'edges_per_agg': 12},  # half=12
    48: {'hosts_per_edge': 24, 'edges_per_agg': 24},  # half=24
}

# Target host counts per port size
TARGET_HOSTS = {
    4:  16,
    24: 108,
    48: 504,
}


class IndustryTopo(Topo):
    """
    3-tier topology using realistic switch port counts (4, 24, or 48).

    Port split rule (same as real data centers):
      Edge switch : ports//2 ports down to hosts
                    ports//2 ports up   to aggregation
      Agg  switch : ports//2 ports down from edge switches
                    ports//2 ports up   to core
      Core switch : one port per aggregation switch

    All hosts use 10.0.0.x/24 with defaultRoute via 10.0.0.254
    so the CPAM controller can discover and VIP-translate all traffic.
    """

    def __init__(self, port_count=24, **opts):
        if port_count not in SWITCH_CONFIGS:
            raise ValueError(
                'port_count must be 4, 24, or 48. Got %d' % port_count
            )
        self.port_count   = port_count
        self.cfg          = SWITCH_CONFIGS[port_count]
        self.target_hosts = TARGET_HOSTS[port_count]
        super(IndustryTopo, self).__init__(**opts)

    def build(self):
        cfg           = self.cfg
        hosts_per_edge = cfg['hosts_per_edge']
        edges_per_agg  = cfg['edges_per_agg']

        # Calculate switch counts to reach target host count
        n_edge = int(math.ceil(
            float(self.target_hosts) / hosts_per_edge
        ))
        n_agg  = int(math.ceil(float(n_edge) / edges_per_agg))
        n_core = 1   # single core switch is sufficient at these scales

        actual_hosts = n_edge * hosts_per_edge

        # ── Core switch ───────────────────────────────────────────────────────
        core = self.addSwitch('core1', cls=OVSKernelSwitch,
                              dpid='%016x' % 1)

        # ── Aggregation switches ──────────────────────────────────────────────
        agg_switches = []
        for a in range(n_agg):
            sw = self.addSwitch(
                'agg%d' % (a + 1),
                cls=OVSKernelSwitch,
                dpid='%016x' % (100 + a + 1)
            )
            agg_switches.append(sw)
            # Connect agg to core
            self.addLink(sw, core)

        # ── Edge switches + Hosts ─────────────────────────────────────────────
        host_id = 1
        for e in range(n_edge):
            edge_sw = self.addSwitch(
                'edge%d' % (e + 1),
                cls=OVSKernelSwitch,
                dpid='%016x' % (200 + e + 1)
            )

            # Connect edge to its aggregation switch
            agg_idx = e // edges_per_agg
            self.addLink(edge_sw, agg_switches[agg_idx])

            # Connect hosts to this edge switch
            for h in range(hosts_per_edge):
                # Spread hosts across octets to avoid /24 overflow:
                # h1-h254   -> 10.0.0.1-254
                # h255-h508 -> 10.0.1.1-254  etc.
                _o2 = (host_id - 1) // 254
                _o3 = ((host_id - 1) % 254) + 1
                ip  = '10.0.%d.%d/8' % (_o2, _o3)
                mac = '00:00:00:00:%02x:%02x' % (
                    host_id // 256,
                    host_id % 256
                )
                host = self.addHost(
                    'h%d' % host_id,
                    ip=ip,
                    mac=mac,
                    defaultRoute=''
                )
                self.addLink(host, edge_sw)
                host_id += 1

        # Store counts for summary printing
        self.n_core  = n_core
        self.n_agg   = n_agg
        self.n_edge  = n_edge
        self.n_hosts = actual_hosts


# =============================================================================
# Runner
# =============================================================================

def run(port_count):
    topo = IndustryTopo(port_count=port_count)
    net  = Mininet(
        topo=topo,
        controller=RemoteController,
        switch=OVSKernelSwitch
    )
    net.start()

    # Print topology summary
    print('')
    print('=' * 55)
    print('  Industry MTD Topology — %d-port switches' % port_count)
    print('=' * 55)
    print('  Core  switches : %d' % topo.n_core)
    print('  Agg   switches : %d' % topo.n_agg)
    print('  Edge  switches : %d' % topo.n_edge)
    print('  Total switches : %d' % (topo.n_core + topo.n_agg + topo.n_edge))
    _last_o2 = (topo.n_hosts - 1) // 254
    _last_o3 = ((topo.n_hosts - 1) % 254) + 1
    print('  Total hosts    : %d  (10.0.0.1 - 10.0.%d.%d)' % (
        topo.n_hosts, _last_o2, _last_o3))
    print('  Total devices  : %d' % (
        topo.n_core + topo.n_agg + topo.n_edge + topo.n_hosts))
    print('  Hosts/edge sw  : %d' % SWITCH_CONFIGS[port_count]['hosts_per_edge'])
    _last_o2 = (topo.n_hosts - 1) // 254
    _vip_start = '10.0.%d.1' % (_last_o2 + 1)
    print('  VIPs start at  : %s' % _vip_start)
    print('  Subnet         : 10.0.0.0/8  (hosts + VIPs across octets)')
    print('=' * 55)
    print('')

    CLI(net)
    net.stop()


# =============================================================================
# Entry point
# =============================================================================

if __name__ == '__main__':
    setLogLevel('info')

    valid = [4, 24, 48]

    if len(sys.argv) < 2:
        print('Usage: sudo python industrytp.py <port_count>')
        print('')
        print('  port_count : 4, 24, or 48')
        print('')
        print('Examples:')
        print('  sudo python industrytp.py 4    # 4-port  switches (~16  hosts)')
        print('  sudo python industrytp.py 24   # 24-port switches (~108 hosts)')
        print('  sudo python industrytp.py 48   # 48-port switches (~504 hosts)')
        sys.exit(1)

    try:
        port_count = int(sys.argv[1])
    except ValueError:
        print('[ERROR] port_count must be a number. Got: %s' % sys.argv[1])
        sys.exit(1)

    if port_count not in valid:
        print('[ERROR] port_count must be 4, 24, or 48. Got: %d' % port_count)
        sys.exit(1)

    run(port_count)
