import json
from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller import event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.packet import packet
from ryu.lib.packet import ethernet
from ryu.lib.packet import icmp
from ryu.lib.packet import arp
from ryu.lib.packet import ipv4
from ryu.lib.packet import tcp
from ryu.lib.packet import udp
from ryu.lib import hub
from random import randint,seed,shuffle
from time import time
from collections import Counter #used to keep track of inactive appearances for IPS


#Custom Event for time out and also triggers IP remapping
class EventMessage(event.EventBase):
    '''Create a custom event with a provided message'''
    def __init__(self, message):
        print("Creating Event")
        super(EventMessage, self).__init__()
        self.msg=message

#Main Application
class MovingTargetDefense(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION] #sets switches to version 1.3 (jordan)
    _EVENTS = [EventMessage] #links even from above (jordan)

    NUM_VIPS = 246 #Customizable number of virtual IPs, doesn't work past 255.
    def start(self):
        '''
            Append a new thread which calls the TimerEventGen function which generates timeout events
            every 30 seconds & sends these events to its listeners
            Reference: https://sourceforge.net/p/ryu/mailman/ryu-devel/?viewmonth=201601&viewday=12
        '''
        super(MovingTargetDefense,self).start()
        self.threads.append(hub.spawn(self.TimerEventGen))
            
    def TimerEventGen(self):
        
        '''
            A function which generates timeout events every 30 seconds
            & sends these events to its listeners
            Reference: https://sourceforge.net/p/ryu/mailman/ryu-devel/?viewmonth=201601&viewday=12
        '''


        while 1:
            hub.sleep(1) 
            self.received_replies = 0
            self.expected_replies = len(self.datapaths)
            
            self.base_packet_counts.clear()
            for dp in self.datapaths: #code used to active function and ask for flow tables (jordan)
                self.flow_mode = "packet_count_base"
                self.logger.info("Base cycle starting")
                self.active_flows_request(dp)
            hub.sleep(3) #gives time for replies to come in (jordan)
            

            self.delta_packet_counts.clear()
            for dp in self.datapaths:
                self.flow_mode = "packet_count_delta"
                self.logger.info("Delta cycle starting")
                self.active_flows_request(dp)
            hub.sleep(3)
            

            self.send_event_to_observers(EventMessage("TIMEOUT"))
            hub.sleep(30) #changes IP every 30 seconds
    
    def __init__(self, *args, **kwargs):
        '''Constructor, used to initialize the member variables'''
        super(MovingTargetDefense, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        self.datapaths=set()
        self.HostAttachments={}
        self.offset_of_mappings=0
        
        self.flow_mode = "packet_count_base" #<- this is used to change the flow requests from gettings IPs to a packet count puller
        self.base_packet_counts = {}
        self.delta_packet_counts = {}
        self.active_ips = set()
        self.expected_replies = 0
        self.received_replies = 0
        
        self.AuthorizedEntities = ['10.0.0.1']
        self.R2V_Mappings = {
            "10.0.0.1": "",
            "10.0.0.2": "",
            "10.0.0.3": "",
            "10.0.0.4": "",
            "10.0.0.5": "",
            "10.0.0.6": "",
            "10.0.0.7": "",
            "10.0.0.8": ""
        }
        self.V2R_Mappings = {}
        self.Resources = self.generateVirtualIPs("10.0.0.9", self.NUM_VIPS) #generates virtual IPs from 10.0.0.9 to 10.0.0.9+NUM_VIPS

    def generateVirtualIPs(self, start_ip: str, count: int) -> list:
        baseParts = start_ip.split('.') # Splits 10.0.0.9 into a list based on .
        base = list(map(int, baseParts)) # Converts each list entry into an integer
    
        ips = []
        for _ in range(count):
            ips.append('.'.join(map(str, base)))
            base[3] += 1  # increment last octet
            # handle overflow to the previous octets
            for i in range(3, 0, -1):  # prevents overflow
                if base[i] > 255: #IPs can only go up to 255 before changing octets
                    base[i] = 0
                    base[i - 1] += 1
        return ips

    
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER) #set_ev basically means listen for this event and run this function when that happens (jordan)
    def handleSwitchFeatures(self, ev):
        '''
            Handles switch feature events sent by the switches to the controller
            the first time switch sends negotiation messages.
            We store the switch info to the datapaths member variable
            & add table miss flow entry to the switches.
            
            #Reference: Simple_Switch
            #http://ryu.readthedocs.io/en/latest/writing_ryu_app.html
        '''
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        self.datapaths.add(datapath)
        # install table-miss flow entry
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions)
          
    def EmptyTable(self,datapath):
        '''
            Empties flow table of a switch!
            Remove Flow rules from switches
            Reference: https://sourceforge.net/p/ryu/mailman/message/32333352/
        '''
        ofProto=datapath.ofproto
        parser = datapath.ofproto_parser
        match=parser.OFPMatch()
        flow_mod=datapath.ofproto_parser.OFPFlowMod(datapath,0,0,0,ofProto.OFPFC_DELETE,0,0,1,ofProto.OFPCML_NO_BUFFER,ofProto.OFPP_ANY,ofProto.OFPG_ANY,0,match=match,instructions=[])
        datapath.send_msg(flow_mod)
        
    #Listen to timeout & update the mappings
    @set_ev_cls(EventMessage)
    def update_resources(self, ev):
        '''
            On timeout, update real-virtual IP mappings while ensuring:
            - Active hosts are preserved
            - vIPs are not duplicated
        '''
        seed(time())
        self.logger.info("Updating vIP mappings...")
        # RY chnages START

        # Shuffle resources for randomness and avoid reuse
        available_resources = self.Resources[:]
        shuffle(available_resources)
        used_vips = set()

        for real_ip in self.R2V_Mappings.keys():
            if real_ip in self.active_ips:
                self.logger.info("Skipping active host %s", real_ip)
                continue

            for vip in available_resources:
                if vip not in used_vips and vip not in self.R2V_Mappings.values():
                    self.logger.info("Assigning %s --> %s", real_ip, vip)
                    self.R2V_Mappings[real_ip] = vip
                    used_vips.add(vip)
                    break
            else:
                self.logger.warning("No available vIP for %s!", real_ip)

        self.V2R_Mappings = {v: k for k, v in self.R2V_Mappings.items()}

        # Remove all existing flows and reinstall default flow entries
        for curSwitch in self.datapaths:
            parser = curSwitch.ofproto_parser
            match = parser.OFPMatch()
            self.EmptyTable(curSwitch)
            ofProto = curSwitch.ofproto
            actions = [parser.OFPActionOutput(ofProto.OFPP_CONTROLLER,
                                            ofProto.OFPCML_NO_BUFFER)]
            self.add_flow(curSwitch, 0, match, actions)
            # Ry changes END
    def isRealIPAddress(self,ipAddr):
        '''Returns True id IP address is real'''
        if ipAddr in self.R2V_Mappings.keys():
            return True
    
    def isVirtualIPAddress(self,ipAddr):
        ''' Returns True if the IP address is virtual'''
        if ipAddr in self.R2V_Mappings.values():
            return True
        
    '''def isAuthorizedEntity(self,ipAddr):
        if ipAddr in self.AuthorizedEntities:
            return True'''
        
    def isDirectContact(self,datapath,ipAddr):
        '''
            Return true if the IP addr host is directky connected to the switch given
            Also assumes that the host is directly connected if it has no information in the hostAttachments Table
        '''
        if ipAddr in self.HostAttachments.keys():
            if self.HostAttachments[ipAddr]==datapath:
                return True
            else:
                return False
        return True
         
    
    def add_flow(self, datapath, priority, match, actions, buffer_id=None, hard_timeout=None): #hanldes installing flow entries with/without timeouts and with/without buffer references
        '''
            Adds flow rules to the switch 
            Reference: Simple_Switch
            http://ryu.readthedocs.io/en/latest/writing_ryu_app.html
        '''
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if buffer_id :
            if hard_timeout==None:
                mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match,
                                    instructions=inst)
            else:
                mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match,
                                    instructions=inst, hard_timeout=hard_timeout)
        else:
            if hard_timeout==None:
                mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst)
            else:
                mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst, hard_timeout=hard_timeout)
        datapath.send_msg(mod)

    def active_flows_request(self, datapath): #datapath is a ryu object representing a switch (jordan)
        parser = datapath.ofproto_parser # I think these 2 lines gives me access to the switches code and protocols and what not
        ofproto = datapath.ofproto

        match = parser.OFPMatch() #gives all flows
        req = parser.OFPFlowStatsRequest(datapath, 0, ofproto.OFPTT_ALL,
                                      ofproto.OFPP_ANY, ofproto.OFPG_ANY,
                                      0,0, match) #openflow create a request message to ask the switch for flow stats. 
                                                    #data path is the target switch, OFPTT_All= all flows tables, 
                                                    #OFPG_Any = flows from any port , ofpg= any group, the zeros mean no cookie filtering, match the match filter means match all
    
        datapath.send_msg(req) #now send all that info just created to the switch and the SWITCH shall reply

    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER) #handles the reply from the switch (jordan)
    def flow_reply_handler(self, ev):
        if self.flow_mode == "packet_count_base":
            for stat in ev.msg.body:
                match_flow = stat.match
                if 'ipv4_src' in match_flow and 'ipv4_dst' in match_flow and 'in_port' in match_flow:
                    flow_id = (match_flow['ipv4_src'], match_flow['ipv4_dst'], match_flow['in_port'])
                    self.base_packet_counts[flow_id] = stat.packet_count
            self.logger.info("Base Reply proccessed")
    
    
        elif self.flow_mode == "packet_count_delta":
            for stat in ev.msg.body:
                match_flow = stat.match
                if 'ipv4_src' in match_flow and 'ipv4_dst' in match_flow and 'in_port' in match_flow:
                    flow_id = (match_flow['ipv4_src'], match_flow['ipv4_dst'], match_flow['in_port'])
                    self.delta_packet_counts[flow_id] = stat.packet_count
            self.received_replies += 1
            self.logger.info(f"Delta Reply proccesed ({self.received_replies}/{self.expected_replies})")
            
            if self.received_replies == self.expected_replies:
                self.logger.info("All replies recieved and starting comparison")
                self.compare_base_and_delta()
                
            
    def compare_base_and_delta(self): #used to compare the two stats pull to find active ips
        from collections import Counter
    
        ip_base_counts = Counter()
        ip_delta_counts = Counter()
    
        for (src_ip, dst_ip, _), count in self.base_packet_counts.items():
            ip_base_counts[src_ip] += count
            ip_base_counts[dst_ip] += count
    
        for (src_ip, dst_ip, _), count in self.delta_packet_counts.items():
            ip_delta_counts[src_ip] += count
            ip_delta_counts[dst_ip] += count
    
        self.active_ips = set()
    
        for ip in ip_delta_counts:
            if ip not in ip_base_counts:
                self.active_ips.add(ip)
            elif ip_delta_counts[ip] > ip_base_counts[ip]:
                self.active_ips.add(ip)
    
        self.logger.info("Comparison has ended")
        self.logger.info("Active IPs based on packet growth: %s", self.active_ips)

    #Packet Handler ICMP & ARP
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER) #call this function when a packet hits controller with no match in flow table
    def handlePacketInEvents(self, ev):
        '''
            Handles Incoming Packets & implements Random Host mutation technique
            by changing src & dst IP addresses of the incoming packets.
            Some part of the code is inspired by Simple_Switch
            http://ryu.readthedocs.io/en/latest/writing_ryu_app.html 
        '''
        actions=[]
        pktDrop=False
        
               
        if ev.msg.msg_len < ev.msg.total_len:
            self.logger.debug("packet truncated: only %s of %s bytes",
                              ev.msg.msg_len, ev.msg.total_len)
            
        msg = ev.msg
        datapath = msg.datapath
        dpid = datapath.id
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']
        pkt = packet.Packet(msg.data)
       
        
        # Extract Ethernet frame first
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        eth_dst = eth.dst
        eth_src = eth.src

        # Store the incoming packet source address, switch & port combination
        self.mac_to_port.setdefault(dpid, {})
        self.mac_to_port[dpid][eth_src] = in_port

        # Learning Mac implementation to avoid flood
        if eth_dst in self.mac_to_port[dpid]:
            out_port = self.mac_to_port[dpid][eth_dst]
        else:
            out_port = ofproto.OFPP_FLOOD

        # Extract all protocol layers at once
        ip_pkt = pkt.get_protocol(ipv4.ipv4)
        arp_pkt = pkt.get_protocol(arp.arp)
        tcp_pkt = pkt.get_protocol(tcp.tcp)
        udp_pkt = pkt.get_protocol(udp.udp)

        # Handle ARP packets
        if arp_pkt:
            print("ARP PACKET FOUND!")
            src = arp_pkt.src_ip
            dst = arp_pkt.dst_ip
            
            '''
                To Implement a Learning MTD, there is a need to know, to which switch, the host is directly connected to.
                So the first time an ARP packet comes in who's src address is real, we store the IP addr-Switch DPID mapping
                into the member variable HostAttachments.
            '''
            if self.isRealIPAddress(src) and src not in self.HostAttachments.keys():
                self.HostAttachments[src] = datapath.id
                
            '''
                Learning MTD implementation
                if src is real change it to virtual no matter wat.
                if dest doesn't have a mapping in my table change to real and flood.
                    This happens only for the first time when we donot know
                    to which switch, the destination host is directly connected to.
                if dst is virtual check if dest is directly connected then change it to real
                else let it pass unchanged.
            '''
            
            if self.isRealIPAddress(src):
                match = parser.OFPMatch(eth_type=0x0806, in_port=in_port, arp_spa=src, arp_tpa=dst)
                spa = self.R2V_Mappings[src]
                print(f"ARP: Changing SRC REAL IP {src} -> Virtual SRC IP {spa}")
                actions.append(parser.OFPActionSetField(arp_spa=spa))
                
            if self.isVirtualIPAddress(dst):
                match = parser.OFPMatch(eth_type=0x0806, in_port=in_port, arp_tpa=dst, arp_spa=src)
                if self.isDirectContact(datapath=datapath.id, ipAddr=self.V2R_Mappings[dst]):
                    tpa = self.V2R_Mappings[dst]
                    print(f"ARP: Changing DST Virtual IP {dst} -> REAL DST IP {tpa}")
                    actions.append(parser.OFPActionSetField(arp_tpa=tpa))
                    
            elif self.isRealIPAddress(dst):
                '''Learn MTD From Flood'''
                match = parser.OFPMatch(eth_type=0x0806, in_port=in_port, arp_spa=src, arp_tpa=dst)
                if not self.isDirectContact(datapath=datapath.id, ipAddr=dst):
                    pktDrop = True
                    print(f"ARP: Dropping from {dpid}")
            else:
                pktDrop = True

        # Handle TCP packets
        elif tcp_pkt and ip_pkt:
            #print("TCP PACKET FOUND!") disabled due to spam
            src = ip_pkt.src
            dst = ip_pkt.dst
            
            if self.isRealIPAddress(src) and src not in self.HostAttachments.keys():
                self.HostAttachments[src] = datapath.id
            
            '''
                Learning MTD implementation
                if src is real change it to virtual no matter wat.
                if dest doesn't have a mapping in my table change to real and flood.
                    This happens only for the first time when we donot know
                    to which switch, the destination host is directly connected to.
                if dst is virtual check if dest is directly connected then change it to real
                else let it pass unchanged.
            '''

            if self.isRealIPAddress(src):
                match = parser.OFPMatch(
                    eth_type=0x0800,
                    ip_proto=6,
                    in_port=in_port,
                    ipv4_src=src,
                    ipv4_dst=dst,
                    tcp_src=tcp_pkt.src_port,
                    tcp_dst=tcp_pkt.dst_port
                )
                ipSrc = self.R2V_Mappings[src]
                #print(f"TCP: Changing SRC REAL IP {src} -> Virtual SRC IP {ipSrc}") disabled due to spam
                actions.append(parser.OFPActionSetField(ipv4_src=ipSrc))

            if self.isVirtualIPAddress(dst):
                match = parser.OFPMatch(
                    eth_type=0x0800,
                    ip_proto=6,
                    in_port=in_port,
                    ipv4_dst=dst,
                    ipv4_src=src,
                    tcp_src=tcp_pkt.src_port,
                    tcp_dst=tcp_pkt.dst_port
                )
                if self.isDirectContact(datapath=datapath.id, ipAddr=self.V2R_Mappings[dst]):
                    ipDst = self.V2R_Mappings[dst]
                    #print(f"TCP: Changing DST Virtual IP {dst} -> Real DST IP {ipDst}") disabled due to spam
                    actions.append(parser.OFPActionSetField(ipv4_dst=ipDst))

            elif self.isRealIPAddress(dst):
                if not self.isDirectContact(datapath=datapath.id, ipAddr=dst):
                    pktDrop = True
                    print(f"TCP: Dropping from {dpid}")
            else:
                pktDrop = True

        # Handle UDP packets
        elif udp_pkt and ip_pkt:
            print("UDP PACKET FOUND!")
            src = ip_pkt.src
            dst = ip_pkt.dst
            
            if self.isRealIPAddress(src) and src not in self.HostAttachments.keys():
                self.HostAttachments[src] = datapath.id

            if self.isRealIPAddress(src):
                match = parser.OFPMatch(
                    eth_type=0x0800,
                    ip_proto=17,
                    in_port=in_port,
                    ipv4_src=src,
                    ipv4_dst=dst,
                    udp_src=udp_pkt.src_port,
                    udp_dst=udp_pkt.dst_port
                )
                ipSrc = self.R2V_Mappings[src]
                print(f"UDP: Changing SRC REAL IP {src} -> Virtual SRC IP {ipSrc}")
                actions.append(parser.OFPActionSetField(ipv4_src=ipSrc))
            if self.isVirtualIPAddress(dst):
                match = parser.OFPMatch(
                    eth_type=0x0800,
                    ip_proto=17,
                    in_port=in_port,
                    ipv4_dst=dst,
                    ipv4_src=src,
                    udp_src=udp_pkt.src_port,
                    udp_dst=udp_pkt.dst_port
                )
                if self.isDirectContact(datapath=datapath.id, ipAddr=self.V2R_Mappings[dst]):
                    ipDst = self.V2R_Mappings[dst]
                    print(f"UDP: Changing DST Virtual IP {dst} -> Real DST IP {ipDst}")
                    actions.append(parser.OFPActionSetField(ipv4_dst=ipDst))
            
            elif self.isRealIPAddress(dst):
                if not self.isDirectContact(datapath=datapath.id, ipAddr=dst):
                    pktDrop = True
                    print(f"UDP: Dropping from {dpid}")
            else:
                pktDrop = True

        # Handle ICMP packets
        elif ip_pkt:
            print("ICMP PACKET FOUND!")
            src = ip_pkt.src
            dst = ip_pkt.dst

            if self.isRealIPAddress(src) and src not in self.HostAttachments.keys():
                self.HostAttachments[src] = datapath.id

            if self.isRealIPAddress(src):
                match = parser.OFPMatch(eth_type=0x0800, in_port=in_port, ipv4_src=src, ipv4_dst=dst)
                ipSrc = self.R2V_Mappings[src]
                print(f"ICMP: Changing SRC REAL IP {src} -> Virtual SRC IP {ipSrc}")
                actions.append(parser.OFPActionSetField(ipv4_src=ipSrc))

            if self.isVirtualIPAddress(dst):
                match = parser.OFPMatch(eth_type=0x0800, in_port=in_port, ipv4_dst=dst, ipv4_src=src)
                if self.isDirectContact(datapath=datapath.id, ipAddr=self.V2R_Mappings[dst]):
                    ipDst = self.V2R_Mappings[dst]
                    print(f"ICMP: Changing DST Virtual IP {dst} -> Real DST IP {ipDst}")
                    actions.append(parser.OFPActionSetField(ipv4_dst=ipDst))

            elif self.isRealIPAddress(dst):
                if not self.isDirectContact(datapath=datapath.id, ipAddr=dst):
                    pktDrop = True
                    print(f"ICMP: Dropping from {dpid}")
            else:
                pktDrop = True

        # Log packet information
        self.logger.info("packet in %s %s %s %s", dpid, eth_src, eth_dst, in_port)
        
        # Add output action if packet shouldn't be dropped
        if not pktDrop:
            actions.append(parser.OFPActionOutput(out_port))
        '''install a flow to avoid packet_in next time'''
        if out_port != ofproto.OFPP_FLOOD:
            '''
                verify if we have a valid buffer_id, if yes avoid to send both flow_mod & packet_out
                Install Flow rules to avoid the packet in message for similar packets.
            '''
            if msg.buffer_id != ofproto.OFP_NO_BUFFER:
                self.add_flow(datapath, 1, match, actions, msg.buffer_id)
                return
            else:
                self.add_flow(datapath, 1, match, actions)    
        data = None
        if msg.buffer_id == ofproto.OFP_NO_BUFFER:
            data = msg.data
        '''
            Build a packet out message & send it to the switch with the action set,
            Action set includes all the IP addres changes & out port actions.
        '''
        out = parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id,
                                  in_port=in_port, actions=actions, data=data)
        '''Send the packet out message to the switch'''
        datapath.send_msg(out)
