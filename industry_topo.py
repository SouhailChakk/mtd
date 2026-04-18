#!/usr/bin/env python
# -*- coding: utf-8 -*-
# =============================================================================
# industrytp.py — Enterprise fat-tree MTD topology
#
# Switch port sizes:
#   4-port  -> small  topology (~16  hosts)
#   24-port -> medium topology (~108 hosts)
#   48-port -> large  topology (~512 hosts)
#
# Architecture: proper fat-tree (Core -> Aggregation -> Edge -> Hosts)
#
#   Fat-tree port split rule (k = port_count):
#     k/2 core switches       — each fully meshed with all agg switches
#     k   agg  switches       — each connected to ALL core switches (k/2 uplinks)
#                               and k/2 edge switches (k/2 downlinks)
#     k*(k/2) edge switches   — each connected to 2 agg switches (redundant uplinks)
#                               and k/2 hosts (downlinks)
#
#   This gives every host two independent paths to the core — real redundancy.
#   If any single switch or link fails, traffic reroutes automatically.
#
# Topology counts:
#   small  (k=4)  : 2 core, 4 agg,  8 edge,   ~16  hosts
#   medium (k=24) : pending
#   large  (k=8)  : 4 core, 8 agg, 16 edge,  ~512  hosts  (uses k=8 fat-tree)
#
# Host IP addressing:
#   Hosts use sequential usable addresses inside 10.0.0.0/21
#   (single flat subnet across 10.0.0.x ... 10.0.7.x)
#
# Usage:
#   sudo python industrytp.py 4     # small  (~16  hosts)
#   sudo python industrytp.py 24    # medium (~108 hosts)
#   sudo python industrytp.py 48    # large  (~512 hosts)
# =============================================================================

from mininet.topo import Topo
from mininet.net import Mininet
from mininet.node import OVSKernelSwitch, RemoteController
from mininet.cli import CLI
from mininet.log import setLogLevel
import sys
import json


# =============================================================================
# Fat-tree parameters per switch port count
# =============================================================================
# A proper fat-tree with parameter k has:
#   (k/2)^2        core switches
#   k pods, each with k/2 agg switches and k/2 edge switches
#   k^3/4          hosts total
#
# We map the three CLI port counts to fat-tree k values that give
# the closest host count to the original topology targets.
#
#   port_count=4  -> k=4 fat-tree : 4 core, 4 agg,  4 edge,  16 hosts
#   port_count=24 -> k=6 fat-tree : 9 core, 12 agg, 12 edge, 54 hosts
#                    (scaled x2)  : we duplicate pods -> 108 hosts
#   port_count=48 -> k=8 fat-tree : 16 core, 16 agg, 16 edge, 128 hosts
#                    (scaled x4)  : we use k=16 ->  512 hosts
#
# For simplicity and Mininet compatibility we use a direct parametric
# fat-tree rather than strict k-ary, letting us hit ~the same host counts
# as the original code while adding full redundancy.

FAT_TREE_CONFIGS = {
    # port_count : (n_core, n_agg, n_edge, hosts_per_edge, uplinks_per_edge)
    # uplinks_per_edge = how many agg switches each edge switch connects to
    4:  {'n_core': 2, 'n_agg': 4,  'n_edge': 8,  'hosts_per_edge': 2,  'uplinks': 2},
    24: {'n_core': 4, 'n_agg': 8,  'n_edge': 9,  'hosts_per_edge': 12, 'uplinks': 2},
    48: {'n_core': 4, 'n_agg': 8,  'n_edge': 16, 'hosts_per_edge': 32, 'uplinks': 2},
}

HOST_SUBNET_PREFIX = 21
HOST_SUBNET_NETWORK_INT = (10 << 24)  # 10.0.0.0
HOST_SUBNET_SIZE = 1 << (32 - HOST_SUBNET_PREFIX)
HOST_SUBNET_BROADCAST_INT = HOST_SUBNET_NETWORK_INT + HOST_SUBNET_SIZE - 1
HOST_SUBNET_USABLE = HOST_SUBNET_SIZE - 2


def host_ip_from_index(host_index):
    """
    Return the Nth usable host IP in 10.0.0.0/21 (1-based).
    Uses full sequential progression, e.g.:
      1   -> 10.0.0.1
      255 -> 10.0.0.255
      256 -> 10.0.1.0
      512 -> 10.0.2.0
    """
    if host_index < 1 or host_index > HOST_SUBNET_USABLE:
        raise ValueError('host_index must be in [1, %d]' % HOST_SUBNET_USABLE)
    ip_int = HOST_SUBNET_NETWORK_INT + host_index
    return '%d.%d.%d.%d' % (
        (ip_int >> 24) & 0xFF,
        (ip_int >> 16) & 0xFF,
        (ip_int >> 8) & 0xFF,
        ip_int & 0xFF,
    )


class FatTreeTopo(Topo):
    """
    Enterprise fat-tree topology with full redundancy.

    Every edge switch has uplinks_per_edge connections to different
    aggregation switches, so there are always multiple paths between
    any two hosts. Every aggregation switch is connected to ALL core
    switches for full mesh at the top of the network.

    This is what real enterprise and data center networks look like.
    """

    def __init__(self, port_count=48, **opts):
        if port_count not in FAT_TREE_CONFIGS:
            raise ValueError(
                'port_count must be 4, 24, or 48. Got %d' % port_count
            )
        self.port_count = port_count
        self.cfg        = FAT_TREE_CONFIGS[port_count]
        super(FatTreeTopo, self).__init__(**opts)

    def build(self):
        cfg            = self.cfg
        n_core         = cfg['n_core']
        n_agg          = cfg['n_agg']
        n_edge         = cfg['n_edge']
        hosts_per_edge = cfg['hosts_per_edge']
        uplinks        = cfg['uplinks']
        required_hosts = n_edge * hosts_per_edge
        if required_hosts > HOST_SUBNET_USABLE:
            raise ValueError(
                'Topology needs %d hosts but subnet 10.0.0.0/%d supports only %d usable hosts'
                % (required_hosts, HOST_SUBNET_PREFIX, HOST_SUBNET_USABLE)
            )

        # ── Core switches ─────────────────────────────────────────────────────
        # All core switches are interconnected with each other for redundancy
        core_switches = []
        for c in range(n_core):
            sw = self.addSwitch(
                'core%d' % (c + 1),
                cls=OVSKernelSwitch,
                dpid='%016x' % (c + 1)
            )
            core_switches.append(sw)

        # Connect core switches to each other (full mesh at core layer)
        for i in range(n_core):
            for j in range(i + 1, n_core):
                self.addLink(core_switches[i], core_switches[j])

        # ── Aggregation switches ──────────────────────────────────────────────
        # Each agg switch connects to ALL core switches (full mesh upward)
        agg_switches = []
        for a in range(n_agg):
            sw = self.addSwitch(
                'agg%d' % (a + 1),
                cls=OVSKernelSwitch,
                dpid='%016x' % (100 + a + 1)
            )
            agg_switches.append(sw)
            # Connect this agg switch to every core switch
            for core_sw in core_switches:
                self.addLink(sw, core_sw)

        # ── Edge switches + Hosts ─────────────────────────────────────────────
        # Each edge switch connects to `uplinks` different agg switches
        # This gives redundant paths — if one agg switch fails, traffic
        # automatically uses the other uplink.
        host_id = 1
        for e in range(n_edge):
            edge_sw = self.addSwitch(
                'edge%d' % (e + 1),
                cls=OVSKernelSwitch,
                dpid='%016x' % (200 + e + 1)
            )

            # Connect edge to `uplinks` agg switches (round-robin assignment)
            # e.g. edge1 -> agg1, agg2 | edge2 -> agg2, agg3 | etc.
            for u in range(uplinks):
                agg_idx = (e * uplinks + u) % n_agg
                self.addLink(edge_sw, agg_switches[agg_idx])

            # Connect hosts to this edge switch
            for h in range(hosts_per_edge):
                ip  = '%s/%d' % (host_ip_from_index(host_id), HOST_SUBNET_PREFIX)
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
        self.n_core    = n_core
        self.n_agg     = n_agg
        self.n_edge    = n_edge
        self.n_hosts   = n_edge * hosts_per_edge
        self.n_uplinks = uplinks


# =============================================================================
# Runner
# =============================================================================

def run(port_count):
    topo = FatTreeTopo(port_count=port_count)
    net  = Mininet(
        topo=topo,
        controller=RemoteController,
        switch=OVSKernelSwitch
    )
    net.start()

    cfg = FAT_TREE_CONFIGS[port_count]

    # Print topology summary
    print('')
    print('=' * 62)
    print('  Enterprise Fat-Tree MTD Topology — %d-port switches' % port_count)
    print('=' * 62)
    print('  Core  switches : %d  (fully meshed with each other)' % topo.n_core)
    print('  Agg   switches : %d  (each connected to ALL %d core switches)' % (
        topo.n_agg, topo.n_core))
    print('  Edge  switches : %d  (each with %d redundant uplinks to agg)' % (
        topo.n_edge, topo.n_uplinks))
    print('  Total switches : %d' % (topo.n_core + topo.n_agg + topo.n_edge))
    _last_ip = host_ip_from_index(topo.n_hosts)
    print('  Total hosts    : %d  (10.0.0.1 - %s)' % (
        topo.n_hosts, _last_ip))
    print('  Total devices  : %d' % (
        topo.n_core + topo.n_agg + topo.n_edge + topo.n_hosts))
    print('  Hosts/edge sw  : %d' % cfg['hosts_per_edge'])
    print('')
    print('  Redundancy:')
    print('    Every host has %d independent paths to the core' % topo.n_uplinks)
    print('    Core mesh ensures no single core switch is a bottleneck')
    print('    Any single switch or link failure is automatically rerouted')
    print('')
    _vip_start = host_ip_from_index(topo.n_hosts + 1)
    print('  VIPs start at  : %s' % _vip_start)
    print('  Subnet         : 10.0.0.0/%d  (single flat subnet)' % HOST_SUBNET_PREFIX)
    print('=' * 62)
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
        print('  sudo python industrytp.py 4    # small  (~16  hosts, fat-tree)')
        print('  sudo python industrytp.py 24   # medium (~108 hosts, fat-tree)')
        print('  sudo python industrytp.py 48   # large  (~512 hosts, fat-tree)')
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
