# Updated mtd_V2.py with fixes for ARP reply handling, MAC learning, and ICMP packet processing

class MTD:
    # Other methods...

    def _handle_arp(self, request):
        # Properly reply to ARP requests for both REAL host IPs and VIPs
        if request.ip in self.real_hosts:
            self._send_arp_reply(request.ip)
        elif request.ip in self.vips:
            self._send_arp_reply(request.ip)

    def _learn_host(self, ip, mac):
        # Track all host MAC addresses and assign initial VIPs
        self.hosts[ip] = mac
        if ip not in self.vips:
            self.vips[ip] = self.assign_vip(ip)

    def _send_arp_reply(self, target_ip):
        # Correct parameter formatting for ARP replies
        # send ARP reply logic

    def handle_icmp(self, packet):
        # New ICMP packet handling with proper flow rules and VIP activity tracking
        if packet.destination in self.vips:
            self.track_icmp_activity(packet)

    def track_icmp_activity(self, packet):
        # Track VIP to REAL mapping
        self.vip_to_real[packet.source] = packet.real_source
        self.vip_last_seen[packet.destination] = packet.timestamp

    # Other methods...

# Existing functionality for VIP rotation, flow rule management, etc. preserved
