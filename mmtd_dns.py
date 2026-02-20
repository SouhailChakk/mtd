# Prompt for Codex: Fix MTD DNS Controller Issues

## Context
I have a DNS-based Moving Target Defense (MTD) Ryu OpenFlow controller (`mtd_dns.py`) that manages Virtual IPs (VIPs) for network hosts. The controller should rotate PRIMARY VIPs every 60 seconds and handle GRACE VIPs properly, but there are critical bugs.

## Expected Behavior

### VIP Lifecycle
1. **PRIMARY VIP Rotation**: Every 60 seconds, each host gets a new PRIMARY VIP. The old PRIMARY VIP moves to GRACE state.
2. **PRIMARY VIPs**: Should NEVER be reclaimed directly - only rotated every 60s.
3. **GRACE VIPs**: 
   - If idle (no active flows) when rotated → reclaim immediately
   - If active (has active flows) when rotated → keep in GRACE until flows end, then reclaim immediately
4. **Activity Detection**: VIP is ACTIVE if `flow_refs > 0`, IDLE if `flow_refs = 0`
5. **Multiple VIPs per Host**: Allowed (PRIMARY + GRACE VIPs can coexist)

### Flow Tracking
- Each flow has a cookie based on the VIP it's associated with
- Forward flows use `src_vip` cookie → increments `flow_refs[src_vip]`
- Reverse flows use `dst_vip` cookie → increments `flow_refs[dst_vip]`
- When flows expire, `flow_refs` is decremented
- GRACE VIPs are reclaimed when `flow_refs = 0`

## Current Problems

### Problem 1: Rotation Happening Every 30s Instead of 60s
**Expected**: Rotation should happen every 60 seconds (`ROTATE_INTERVAL = 60`)
**Actual**: Rotation appears to be happening every 30 seconds

**Code to Check**:
- `_rotation_loop()` function - verify it only sleeps for `ROTATE_INTERVAL` (60s)
- Check if there are multiple rotation loops or timers
- Verify `ROTATE_INTERVAL = 60` constant

### Problem 2: Premature Reclamation During Active Ping
**Expected**: When actively pinging a host, both source and destination VIPs should be marked ACTIVE and not reclaimed
**Actual**: Destination VIP is being reclaimed even during active ping

**Example**:
- User pings `h1 -> h2` (10.0.0.1 -> 10.0.0.2)
- Source VIP (10.0.0.13) is marked ACTIVE ✓
- Destination VIP (10.0.0.14) is marked IDLE ✗
- Destination VIP gets reclaimed even though ping is active ✗

**Root Cause Suspected**:
- Reverse flow might not be installed (check if `dst_vip_mac` is missing)
- Reverse flow cookie might be wrong (should use `dst_vip` cookie, not `src_vip`)
- `flow_refs[dst_vip]` is not being incremented

**Code to Check**:
- `_handle_real_to_real()` - verify reverse flow is installed with `dst_vip` cookie
- `_handle_real_to_vip()` - verify reverse flow is installed with `dst_vip` cookie
- Check if `dst_vip_mac` is available when installing reverse flows
- Verify `_add_flow()` increments `flow_refs` correctly for both forward and reverse flows

### Problem 3: TCP/UDP Sessions Not Working
**Expected**: TCP/UDP sessions (like `iperf`) should work correctly
**Actual**: `iperf` shows "connect failed: Operation now in progress"

**Root Cause Suspected**:
- Flow matching might be missing protocol-specific fields (TCP/UDP ports)
- Reverse flow matching might be incorrect
- Flow installation timing (packet-out before flow install for TCP SYN)

**Code to Check**:
- `_extract_l4_match_fields()` - verify it extracts TCP/UDP ports correctly
- `_build_ip_match()` or equivalent - verify protocol-specific matching
- Verify `_send_packet_out()` is called BEFORE `_add_flow()` for TCP SYN packets
- Check reverse flow matches use swapped ports correctly

## Key Code Sections

### Flow Installation
```python
def _add_flow(self, dp, priority, match, actions, table_id=0, idle_timeout=0, hard_timeout=0, buffer_id=None, cookie=0):
    # Should increment flow_refs[vip] when cookie has COOKIE_BASE
    if cookie & self.COOKIE_BASE:
        vip = self._cookie_vip_ip(cookie)
        self.vip_flow_refs[vip] = self.vip_flow_refs.get(vip, 0) + 1
```

### Reverse Flow Installation (CRITICAL)
```python
# In _handle_real_to_real() and _handle_real_to_vip():
# Reverse flow MUST use dst_vip cookie to track destination VIP activity
cookie_rev = self._vip_cookie(dst_vip)  # NOT src_vip!
self._add_flow(..., cookie=cookie_rev, ...)
```

### Rotation Logic
```python
def _rotation_loop(self):
    while True:
        hub.sleep(self.ROTATE_INTERVAL)  # Should be 60s
        # Rotate PRIMARY VIPs
        # Move old VIP to GRACE
        # Check flow_refs to determine if idle or active
```

## What Needs to Be Fixed

1. **Verify rotation interval**: Ensure rotation happens exactly every 60s, not 30s
2. **Fix reverse flow installation**: Ensure reverse flows are ALWAYS installed with `dst_vip` cookie when traffic is bidirectional
3. **Fix flow_refs tracking**: Both forward and reverse flows must increment `flow_refs` for their respective VIPs
4. **Fix TCP/UDP matching**: Ensure protocol-specific fields (ports) are included in flow matches
5. **Fix flow installation order**: Send packet-out BEFORE installing flow for TCP SYN packets
6. **Add comprehensive logging**: Log when reverse flows fail to install and why
