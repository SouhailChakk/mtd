#!/usr/bin/env bash
# =============================================================================
#  CPAM MTD — NSDI Benchmark Script  (v3)
#
#  TWO TRAFFIC MODELS — used for different metric groups:
#
#  MODEL 1 — Fixed pairs (one long-lived flow per pair)
#    N/2 concurrent flows, every host talks to exactly one other host.
#    Good for: ICMP latency, TCP throughput, TCP session continuity,
#              UDP jitter/loss, controller overhead.
#    Traffic budget (DUR=120):
#      Small  ( 16 hosts,   8 pairs): UDP@5M →   40 Mbps, TCP → host-limited
#      Medium (100 hosts,  50 pairs): UDP@5M →  250 Mbps, TCP → host-limited
#      Large  (500 hosts, 250 pairs): UDP@5M → 1.25 Gbps, TCP → host-limited
#
#  MODEL 2 — Connection churn (rapid short TCP connections per pair)
#    Same N/2 pairs but each fires repeated 1-second TCP connections
#    back-to-back. Generates high PacketIn event rate without flooding
#    bandwidth. Used exclusively for controller-plane metrics.
#    Good for: FSR (N1), RPPT under load (N3), NAT pressure (N5).
#    Traffic budget: ~1 conn/sec/pair × DUR seconds × N/2 pairs
#      Small  :   8 pairs →  ~8  conns/sec peak controller event rate
#      Medium :  50 pairs →  ~50 conns/sec
#      Large  : 250 pairs → ~250 conns/sec  <- this is what tests scale
#
#  METRICS:
#    Original (preserved):
#      [A]   ICMP Latency             — ping RTT, min/avg/max, loss
#      [B]   TCP Throughput           — iperf2 concurrent flows
#      [C]   TCP Session Continuity   — long-lived flow across VIP rotations
#      [D+E] UDP Jitter + Loss        — iperf2 -u @ 5 Mbps/pair
#      [F]   Controller CPU + Mem     — pidstat on ryu-manager
#      [1]   §5.1.1 Topology Discovery — parsed from Ryu log
#      [2]   §5.1.3 Async Msg Rate    — churn-based, controller event rate
#      [3]   §5.1.4 RPPT (idle)       — parsed from Ryu log
#      [4]   §5.2.3 Forwarding Table  — OVS flow count snapshots
#      [5]   §5.4.2 NRT               — link failure simulation
#
#    New NSDI additions:
#      [N1]  Flow Setup Rate (FSR)    — §5.2.1: flows/sec during churn
#      [N2]  RPPT Percentiles         — p50/p95/p99 from idle RPPT events
#      [N3]  RPPT Under Load          — p50/p95/p99 during churn phase
#      [N4]  VIP Reclamation Lag      — lived_ms from Ryu log
#      [N5]  Scalability Snapshot     — structured per-topology summary
#                                       for cross-scale comparison
#
#  Usage:
#    sudo ./benchmark_nsdi.sh [DURATION] [LABEL] [RYU_LOG] [TOPOLOGY]
#
#    TOPOLOGY: small | medium | large  (default: small)
#      small  — 4-port  switches, ~16  hosts
#      medium — 24-port switches, ~100 hosts
#      large  — 48-port switches, ~500 hosts
#
#  Examples:
#    sudo ./benchmark_nsdi.sh 120 baseline_small  /var/log/ryu.log small
#    sudo ./benchmark_nsdi.sh 120 baseline_medium /var/log/ryu.log medium
#    sudo ./benchmark_nsdi.sh 120 baseline_large  /var/log/ryu.log large
#
#  10-run loop per topology (RFC 8456 §4.7):
#    for TOPO in small medium large; do
#      for i in {1..10}; do
#        sudo ./benchmark_nsdi.sh 120 mtd_${TOPO}_iter${i} \
#             /var/log/ryu.log ${TOPO}
#      done
#    done
#
#  Controller log tokens required:
#    RPPT_MEASURED: key=(...) elapsed_ms=X.XXX
#    VIP_RECLAIMED: vip=X.X.X.X lived_ms=X.XXX
# =============================================================================

set -uo pipefail

# Trap errors for debugging — print line number when something fails
trap 'echo "[ERROR] Script failed at line $LINENO — command: $BASH_COMMAND" >&2' ERR

# ── Arguments ─────────────────────────────────────────────────────────────────
DUR="${1:-120}"
LABEL="${2:-run}"
RYU_LOG="${3:-/var/log/ryu.log}"
TOPOLOGY="${4:-small}"
LONG_DUR="$((DUR * 2))"
TS="$(date +%Y%m%d_%H%M%S)"
OUTDIR="cpam_nsdi_${LABEL}_${TS}"
mkdir -p "$OUTDIR"

# ── Topology-aware parameters ─────────────────────────────────────────────────
#
# CHURN_CONNS: number of short TCP connections fired per pair in Model 2.
#   Each connection = 1 new flow = 1 PacketIn to the controller.
#   Fewer conns on large topology because 250 pairs × N conns already
#   generates plenty of controller events without overloading the host.
#
# The flood BW steps in the original §5.1.3 test are also capped per
# topology to keep total bandwidth within safe Mininet limits:
#   small  (  8 pairs × 20M peak) =  160 Mbps
#   medium ( 50 pairs × 10M peak) =  500 Mbps
#   large  (250 pairs ×  4M peak) = 1000 Mbps

case "$TOPOLOGY" in
    small)
        TOPO_LABEL="Small (~16 hosts, 4-port switches)"
        FLOOD_BW_STEPS=("1M" "5M" "10M" "20M")
        CHURN_CONNS=60
        CHURN_CONN_DUR=1
        ;;
    medium)
        TOPO_LABEL="Medium (~100 hosts, 24-port switches)"
        FLOOD_BW_STEPS=("1M" "5M" "10M")
        CHURN_CONNS=40
        CHURN_CONN_DUR=1
        ;;
    large)
        TOPO_LABEL="Large (~500 hosts, 48-port switches)"
        FLOOD_BW_STEPS=("1M" "4M")
        CHURN_CONNS=20
        CHURN_CONN_DUR=1
        ;;
    *)
        echo "[ERROR] Unknown topology: '$TOPOLOGY'. Use: small | medium | large"
        exit 1
        ;;
esac

CHURN_DUR=$(( CHURN_CONNS * CHURN_CONN_DUR ))
[[ "$CHURN_DUR" -gt "$DUR" ]] && CHURN_DUR="$DUR"

# ── Banner ────────────────────────────────────────────────────────────────────
cat << BANNER
╔══════════════════════════════════════════════════════════════════╗
║         CPAM MTD NSDI Benchmark v3 — RFC 8456 Suite              ║
╠══════════════════════════════════════════════════════════════════╣
║  Label      : ${LABEL}
║  Topology   : ${TOPO_LABEL}
║  Duration   : ${DUR}s per QoS test  (long TCP: ${LONG_DUR}s)
║  Churn      : ${CHURN_DUR}s  (${CHURN_CONNS} conns/pair x ${CHURN_CONN_DUR}s each)
║  Flood steps: ${FLOOD_BW_STEPS[*]}
║  Ryu log    : ${RYU_LOG}
║  Output     : ${OUTDIR}
╠══════════════════════════════════════════════════════════════════╣
║  MODEL 1 (fixed pairs, long-lived flows) -> QoS metrics A B C D E
║  MODEL 2 (conn churn, short connections) -> ctrl metrics 2 N1 N3
╚══════════════════════════════════════════════════════════════════╝
BANNER

# ── Tool checks ───────────────────────────────────────────────────────────────
MISSING=0
for bin in mnexec iperf ping awk sed grep pgrep ovs-vsctl ovs-ofctl date bc; do
    command -v "$bin" >/dev/null 2>&1 || { echo "[ERROR] Missing: $bin"; MISSING=1; }
done
[[ "$MISSING" -eq 1 ]] && exit 1

HAS_PIDSTAT=1
command -v pidstat >/dev/null 2>&1 || {
    HAS_PIDSTAT=0
    echo "[WARN] pidstat not found — install: sudo apt-get install -y sysstat"
}

if [[ ! -f "$RYU_LOG" ]]; then
    echo "[WARN] Ryu log not found at $RYU_LOG"
    echo "[WARN] RPPT, FSR, VIP Reclamation metrics require Ryu log"
    echo "[WARN] To enable: ryu-manager app.py 2>&1 | tee $RYU_LOG"
    RYU_LOG=""
fi

# ── Discover Mininet host PIDs and IPs ────────────────────────────────────────
echo ""
echo "[INIT] Discovering Mininet hosts..."
declare -A HOST_PIDS
declare -A HOST_IPS
declare -A HOST_VIPS   # real IP -> current primary VIP (from /tmp/mtd_vip_mapping.json)

for i in $(seq 1 1000); do
    pid="$(pgrep -n -f " mininet:h${i}$" 2>/dev/null || true)"
    [[ -z "$pid" ]] && break
    HOST_PIDS["h${i}"]="$pid"
    ip="$(mnexec -a "$pid" ip -4 addr show 2>/dev/null         | awk '/inet /{print $2}'         | grep "^10\."         | head -1         | cut -d/ -f1 || true)"
    HOST_IPS["h${i}"]="${ip:-unknown}"
done

FOUND="${#HOST_PIDS[@]}"
echo "[INIT] Found $FOUND hosts"
[[ "$FOUND" -lt 2 ]] && { echo "[ERROR] Need at least 2 hosts. Is Mininet running?"; exit 1; }

# ── Controller PID ────────────────────────────────────────────────────────────
RYUPID="$(pgrep -n -f 'ryu-manager' 2>/dev/null || true)"
[[ -z "$RYUPID" ]] && echo "[WARN] ryu-manager not found — controller metrics skipped"
[[ -n "$RYUPID" ]] && echo "[INIT] Ryu PID=$RYUPID"

# ── Build fixed pairs ─────────────────────────────────────────────────────────
# Pairing strategy: sort hosts by name, split in half, pair i with i+HALF.
# This maximises the chance that traffic crosses switches rather than
# staying on the same edge switch — which matters for realistic flow-table
# and controller event measurements.
declare -a PAIRS_SRC=()
declare -a PAIRS_DST=()
HOSTS_SORTED=($(echo "${!HOST_PIDS[@]}" | tr ' ' '\n' | sort -V))
HALF=$(( ${#HOSTS_SORTED[@]} / 2 ))

for i in $(seq 0 $((HALF - 1))); do
    src="${HOSTS_SORTED[$i]}"
    dst="${HOSTS_SORTED[$((i + HALF))]}"
    if [[ -n "${HOST_PIDS[$src]:-}" && -n "${HOST_PIDS[$dst]:-}" ]]; then
        PAIRS_SRC+=("$src")
        PAIRS_DST+=("$dst")
    fi
done

NUM_PAIRS="${#PAIRS_SRC[@]}"
echo "[INIT] Fixed pairs: $NUM_PAIRS (first half of sorted hosts -> second half)"
echo "[INIT] Traffic model 1: each host talks to exactly one other host"
echo "[INIT] Traffic model 2: same pairs, but $CHURN_CONNS short conns each"

if [[ "$TOPOLOGY" == "small" ]]; then
    for i in $(seq 0 $((NUM_PAIRS - 1))); do
        echo "  ${PAIRS_SRC[$i]} (${HOST_IPS[${PAIRS_SRC[$i]}]}) -> \
${PAIRS_DST[$i]} (${HOST_IPS[${PAIRS_DST[$i]}]})"
    done
else
    echo "  (pair list suppressed for $TOPOLOGY — $NUM_PAIRS total pairs)"
fi
echo ""

# ── Look up current primary VIPs from controller mapping file ─────────────────
# The controller writes /tmp/mtd_vip_mapping.json: {"real_ip": "vip", ...}
# Clients must connect to VIPs, not real IPs, so traffic goes through the
# MTD translation path (RPPT, session tracking, VIP rotation all apply).
# Servers listen on real IPs — the controller rewrites dst before delivery.
VIP_MAPPING="/tmp/mtd_vip_mapping.json"
get_vip() {
    local real_ip="$1"
    if [[ -f "$VIP_MAPPING" ]]; then
        local vip
        vip="$(python3 -c "
import json
m = json.load(open('$VIP_MAPPING'))
print(m.get('$real_ip', ''))
" 2>/dev/null || true)"
        [[ -n "$vip" ]] && echo "$vip" && return
    fi
    echo "$real_ip"
}

VIP_LOOKUP_HELPER="/tmp/cpam_vip_lookup.py"
ensure_vip_lookup_helper() {
    cat > "$VIP_LOOKUP_HELPER" <<'PY'
#!/usr/bin/env python3
import json
import sys

if len(sys.argv) < 2:
    print("")
    raise SystemExit(0)

real_ip = sys.argv[1]
mapping_file = sys.argv[2] if len(sys.argv) > 2 else "/tmp/mtd_vip_mapping.json"

try:
    with open(mapping_file, "r", encoding="utf-8") as f:
        mapping = json.load(f)
except Exception:
    mapping = {}

print(mapping.get(real_ip, real_ip))
PY
    chmod +x "$VIP_LOOKUP_HELPER" 2>/dev/null || true
}

echo "[INIT] Loading VIP mappings from $VIP_MAPPING ..."
for hname in "${!HOST_IPS[@]}"; do
    real="${HOST_IPS[$hname]}"
    if [[ "$real" != "unknown" ]]; then
        vip="$(get_vip "$real")"
        HOST_VIPS["$hname"]="$vip"
    else
        HOST_VIPS["$hname"]="unknown"
    fi
done

# Warn if VIPs not loaded yet — controller may still be discovering hosts
VIP_MISSING=0
for hname in "${HOSTS_SORTED[@]}"; do
    [[ "${HOST_VIPS[$hname]:-unknown}" == "unknown" || "${HOST_VIPS[$hname]:-}" == "${HOST_IPS[$hname]:-}" ]] && VIP_MISSING=$((VIP_MISSING + 1))
done
if [[ "$VIP_MISSING" -gt 0 ]]; then
    echo "[WARN] $VIP_MISSING host(s) have no VIP yet — controller may still be discovering."
    echo "[WARN] Wait for all BIND: log lines in Ryu before running the benchmark."
else
    echo "[INIT] All $FOUND hosts have VIPs assigned."
fi

if [[ "$TOPOLOGY" == "small" ]]; then
    for i in $(seq 0 $((NUM_PAIRS - 1))); do
        src="${PAIRS_SRC[$i]}"
        dst="${PAIRS_DST[$i]}"
        echo "  $src (real=${HOST_IPS[$src]} vip=${HOST_VIPS[$src]:-N/A}) -> $dst (real=${HOST_IPS[$dst]} vip=${HOST_VIPS[$dst]:-unknown})"
    done
fi
echo ""

# ── Helpers ───────────────────────────────────────────────────────────────────
# Refresh HOST_VIPS from mapping file — call before each test phase
# since VIPs rotate every 60s and we want the latest primary VIP per host.
refresh_vips() {
    local updated=0
    for hname in "${!HOST_IPS[@]}"; do
        real="${HOST_IPS[$hname]}"
        [[ "$real" == "unknown" ]] && continue
        vip="$(get_vip "$real")"
        if [[ -n "$vip" && "$vip" != "${HOST_VIPS[$hname]:-}" ]]; then
            HOST_VIPS["$hname"]="$vip"
            updated=$((updated + 1))
        fi
    done
    [[ "$updated" -gt 0 ]] && echo "[VIP] Refreshed $updated VIP mapping(s) from $VIP_MAPPING" || true
}

stop_all_iperf() {
    for hname in "${!HOST_PIDS[@]}"; do
        mnexec -a "${HOST_PIDS[$hname]}" \
            bash -lc "pkill -f '^iperf' 2>/dev/null || true" 2>/dev/null || true
    done
    sleep 1
}

dump_ovs() {
    local tag="$1"
    local outfile="${OUTDIR}/ovs_${tag}.txt"
    {
        echo "=== OVS Snapshot: $tag @ $(date -Ins) ==="
        local ALL_BRIDGES TOTAL=0
        ALL_BRIDGES="$(ovs-vsctl list-br 2>/dev/null || true)"
        for sw in $ALL_BRIDGES; do
            echo "--- $sw ---"
            ovs-ofctl -O OpenFlow13 dump-flows "$sw" 2>/dev/null || true
            local count
            count="$(ovs-ofctl -O OpenFlow13 dump-flows "$sw" 2>/dev/null \
                     | grep -c 'n_packets' 2>/dev/null || echo 0)"
            echo "$sw flow_count=$count"
            TOTAL=$((TOTAL + count))
        done
        echo "TOTAL_FLOWS=$TOTAL"
    } > "$outfile" 2>&1
}

count_total_flows() {
    local total=0 br c
    for br in $(ovs-vsctl list-br 2>/dev/null || true); do
        c="$(ovs-ofctl -O OpenFlow13 dump-flows "$br" 2>/dev/null \
             | grep -c 'n_packets' 2>/dev/null || echo 0)"
        total=$((total + c))
    done
    echo "$total"
}

log_step() {
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "  $1"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
}

# Compute full stats from a file of one float per line.
# Outputs: Count, Mean, Std, 95% CI, Min, Max, p50, p95, p99
compute_stats() {
    local datafile="$1"
    awk '
    BEGIN { n=0; sum=0; min=1e18; max=-1e18; ss=0 }
    /^[0-9]/ {
        n++; v=$1; sum+=v; vals[n]=v
        if (v < min) min=v
        if (v > max) max=v
    }
    END {
        if (n == 0) { print "  No data"; exit }
        mean = sum / n
        for (i=1; i<=n; i++) ss += (vals[i] - mean)^2
        std  = (n > 1) ? sqrt(ss / (n-1)) : 0
        ci   = 1.96 * std / sqrt(n)

        for (i=1; i<=n; i++)
            for (j=i+1; j<=n; j++)
                if (vals[j] < vals[i]) { t=vals[i]; vals[i]=vals[j]; vals[j]=t }

        p50_i = int(0.50*n + 0.5); if (p50_i<1) p50_i=1; if (p50_i>n) p50_i=n
        p95_i = int(0.95*n + 0.5); if (p95_i<1) p95_i=1; if (p95_i>n) p95_i=n
        p99_i = int(0.99*n + 0.5); if (p99_i<1) p99_i=1; if (p99_i>n) p99_i=n

        printf "  Count  : %d\n",       n
        printf "  Mean   : %.3f ms\n",  mean
        printf "  Std Dev: %.3f ms\n",  std
        printf "  95%% CI : +/-%.3f ms\n", ci
        printf "  Min    : %.3f ms\n",  min
        printf "  Max    : %.3f ms\n",  max
        printf "  p50    : %.3f ms\n",  vals[p50_i]
        printf "  p95    : %.3f ms\n",  vals[p95_i]
        printf "  p99    : %.3f ms\n",  vals[p99_i]
    }' "$datafile"
}

extract_rppt_values() {
    local lines="$1" outfile="$2"
    echo "$lines" | grep -oP 'elapsed_ms=\K[0-9.]+' > "$outfile" || true
}

# ── Ryu log start position ────────────────────────────────────────────────────
RYU_LOG_START=0
if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
    RYU_LOG_START="$(wc -l < "$RYU_LOG" | tr -d " \n")"
    echo "[INIT] Ryu log start: line $RYU_LOG_START"
fi

# ── Start pidstat ─────────────────────────────────────────────────────────────
PIDSTAT_PID=""
if [[ "$HAS_PIDSTAT" -eq 1 && -n "$RYUPID" ]]; then
    TOTAL_DURATION=$(( DUR * 5 + LONG_DUR + CHURN_DUR + 300 ))
    pidstat -rud -h -p "$RYUPID" 1 "$TOTAL_DURATION" \
        > "${OUTDIR}/F_controller_pidstat.txt" 2>&1 &
    PIDSTAT_PID="$!"
    echo "[F] pidstat started (PID=$PIDSTAT_PID, window=${TOTAL_DURATION}s)"
fi

# =============================================================================
# [1] RFC 8456 §5.1.1 — TOPOLOGY DISCOVERY TIME
# =============================================================================
log_step "[1] RFC 8456 §5.1.1 — Topology Discovery Time"
dump_ovs "initial"

{
    echo "=== RFC 8456 §5.1.1 Topology Discovery Time ==="
    echo "Topology : $TOPO_LABEL"
    echo "Timestamp: $(date -Ins)"
    echo ""
    if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
        DISCO_LINE="$(grep 'TOPO_DISCOVERY_COMPLETE' "$RYU_LOG" | tail -1 || true)"
        if [[ -n "$DISCO_LINE" ]]; then
            echo "Found: $DISCO_LINE"
            ELAPSED="$(echo "$DISCO_LINE" | grep -oP 'elapsed=\K[0-9.]+' || echo 'N/A')"
            echo "Discovery elapsed: ${ELAPSED}s"
        else
            echo "TOPO_DISCOVERY_COMPLETE not found in log."
            echo "Log token required: TOPO_DISCOVERY_COMPLETE elapsed=X.XXX"
        fi
    else
        echo "No Ryu log available."
    fi
    echo ""
    ovs-vsctl show 2>/dev/null || true
} > "${OUTDIR}/1_topology_discovery_time.txt"
cat "${OUTDIR}/1_topology_discovery_time.txt"

# =============================================================================
# [D+E] MODEL 1 — UDP JITTER + PACKET LOSS
# =============================================================================
log_step "[D+E] UDP Jitter + Loss — Model 1 — ${NUM_PAIRS} pairs (${DUR}s @ 5 Mbps/pair)"
refresh_vips
stop_all_iperf
dump_ovs "pre_udp"

for i in $(seq 0 $((NUM_PAIRS - 1))); do
    dst="${PAIRS_DST[$i]}"
    mnexec -a "${HOST_PIDS[$dst]}" bash -lc "iperf -s -u -i 1" \
        > "${OUTDIR}/DE_udp_server_${dst}.txt" 2>&1 &
done
sleep 1

UDP_PIDS=()
for i in $(seq 0 $((NUM_PAIRS - 1))); do
    src="${PAIRS_SRC[$i]}"
    dst="${PAIRS_DST[$i]}"
    dst_ip="${HOST_VIPS[$dst]:-${HOST_IPS[$dst]}}"   # connect to VIP
    mnexec -a "${HOST_PIDS[$src]}" bash -lc \
        "iperf -c ${dst_ip} -u -b 5M -t ${DUR} -i 1" \
        > "${OUTDIR}/DE_udp_client_${src}_to_${dst}.txt" 2>&1 &
    UDP_PIDS+=("$!")
done

TOTAL_UDP_BW="$(echo "$NUM_PAIRS * 5" | bc)"
echo "[D+E] ${#UDP_PIDS[@]} UDP flows x 5 Mbps = ${TOTAL_UDP_BW} Mbps total for ${DUR}s..."
sleep "$((DUR / 2))"
dump_ovs "mid_udp"
for pid in "${UDP_PIDS[@]}"; do wait "$pid" 2>/dev/null || true; done
sleep 1
stop_all_iperf

{
    echo "=== UDP Jitter + Packet Loss Summary ==="
    echo "Topology  : $TOPO_LABEL   Pairs: $NUM_PAIRS"
    echo "Total BW  : ${TOTAL_UDP_BW} Mbps  (5 Mbps/pair)"
    echo ""
    printf "%-30s %-12s %-15s\n" "Pair" "Jitter(ms)" "Loss(lost/total)"
    printf "%-30s %-12s %-15s\n" \
        "------------------------------" "----------" "---------------"
    for i in $(seq 0 $((NUM_PAIRS - 1))); do
        src="${PAIRS_SRC[$i]}"
        dst="${PAIRS_DST[$i]}"
        srv="${OUTDIR}/DE_udp_server_${dst}.txt"
        # Parse from the iperf2 summary line: "0.0-XX.X sec ... Jitter Lost/Total"
        # Exclude "out-of-order" lines and per-second interval lines by matching
        # only lines that start with the full duration (0.0-) and have ms in them
        _srv_summary="$(grep -E '0\.0-[0-9]' "$srv" 2>/dev/null | \
                        grep -v 'out-of-order' | tail -1)"
        jitter="$(echo "$_srv_summary" | \
                  awk '{for(i=1;i<=NF;i++) if($i~/ms$/) {gsub("ms","",$i); print $i; exit}}' \
                  || echo 'N/A')"
        loss="$(echo "$_srv_summary" | \
                grep -oE '[0-9]+/ +[0-9]+' | tr -d ' ' | tail -1 || \
                echo "$_srv_summary" | grep -oE '[0-9]+/[0-9]+' | tail -1 || \
                echo 'N/A')"
        printf "%-30s %-12s %-15s\n" "${src}->${dst}" "$jitter" "$loss"
    done
} > "${OUTDIR}/DE_udp_summary.txt"
cat "${OUTDIR}/DE_udp_summary.txt"

# [A] MODEL 1 — ICMP LATENCY
log_step "[A] ICMP Latency — Model 1 — ${NUM_PAIRS} fixed pairs (${DUR}s)"

refresh_vips
PING_COUNT="$((DUR * 5))"
PING_PIDS=()

for i in $(seq 0 $((NUM_PAIRS - 1))); do
    src="${PAIRS_SRC[$i]}"
    dst="${PAIRS_DST[$i]}"
    dst_ip="${HOST_VIPS[$dst]:-${HOST_IPS[$dst]}}"   # ping to VIP
    mnexec -a "${HOST_PIDS[$src]}" bash -lc \
        "ping -i 0.2 -c ${PING_COUNT} ${dst_ip}" \
        > "${OUTDIR}/A_latency_${src}_to_${dst}.txt" 2>&1 &
    PING_PIDS+=("$!")
done

echo "[A] ${#PING_PIDS[@]} ping streams x ${PING_COUNT} packets each..."
dump_ovs "during_ping"
for pid in "${PING_PIDS[@]}"; do wait "$pid" 2>/dev/null || true; done

{
    echo "=== ICMP Latency Summary (RFC 8456 §5.1.2) ==="
    echo "Topology : $TOPO_LABEL   Pairs: $NUM_PAIRS"
    echo ""
    printf "%-30s %-10s %-10s %-10s %-10s\n" \
        "Pair" "Min(ms)" "Avg(ms)" "Max(ms)" "Loss(%)"
    printf "%-30s %-10s %-10s %-10s %-10s\n" \
        "------------------------------" "--------" "--------" "--------" "--------"

    SUM_AVG=0
    N_RTT=0
    for i in $(seq 0 $((NUM_PAIRS - 1))); do
        src="${PAIRS_SRC[$i]}"
        dst="${PAIRS_DST[$i]}"
        f="${OUTDIR}/A_latency_${src}_to_${dst}.txt"
        rtt="$(grep 'min/avg/max' "$f" 2>/dev/null | \
               awk -F'[=/]' '{printf "%-10s %-10s %-10s", $5, $6, $7}' \
               || echo "N/A        N/A        N/A")"
        loss="$(grep 'packet loss' "$f" 2>/dev/null | awk '{print $6}' || echo "N/A")"
        printf "%-30s %s %-10s\n" "${src}->${dst}" "$rtt" "$loss"
        avg_val="$(grep 'min/avg/max' "$f" 2>/dev/null | awk -F'[=/]' '{print $6}' || echo '')"
        if [[ -n "$avg_val" && "$avg_val" =~ ^[0-9.]+$ ]]; then
            SUM_AVG="$(echo "$SUM_AVG + $avg_val" | bc)"
            N_RTT=$((N_RTT + 1))
        fi
    done
    echo ""
    if [[ "$N_RTT" -gt 0 ]]; then
        MEAN_RTT="$(echo "scale=3; $SUM_AVG / $N_RTT" | bc)"
        echo "Topology mean RTT : ${MEAN_RTT} ms  (across $N_RTT pairs)"
    fi
} > "${OUTDIR}/A_latency_summary.txt"
cat "${OUTDIR}/A_latency_summary.txt"

# =============================================================================
# [2 + N1 + N3] MODEL 2 — CONNECTION CHURN PHASE
#
#  Each pair fires CHURN_CONNS short (1-second) TCP connections back-to-back.
#  Every new TCP connection = unmatched flow = PacketIn to the controller
#  = VIP lookup + NAT entry + FlowMod install.
#
#  This stresses the controller at a rate proportional to the number of pairs:
#    Small  :   8 pairs x 60 conns =   480 total controller events
#    Medium :  50 pairs x 40 conns = 2,000 total controller events
#    Large  : 250 pairs x 20 conns = 5,000 total controller events
#
#  Three metrics share this window:
#    [2]  §5.1.3 Async Msg Rate  — estimated events/sec, saturation check
#    [N1] Flow Setup Rate (FSR)  — OVS delta flows / elapsed time
#    [N3] RPPT Under Load        — RPPT events from Ryu log during window
# =============================================================================
log_step "[2+N1+N3] Model 2 — Connection Churn (${CHURN_DUR}s, ${CHURN_CONNS} conns/pair)"

refresh_vips
ensure_vip_lookup_helper
stop_all_iperf
dump_ovs "pre_churn"

TOTAL_CHURN_EVENTS=$(( NUM_PAIRS * CHURN_CONNS ))
echo "[Churn] Topology    : $TOPO_LABEL"
echo "[Churn] Pairs       : $NUM_PAIRS"
echo "[Churn] Conns/pair  : $CHURN_CONNS x ${CHURN_CONN_DUR}s"
echo "[Churn] Total events: ~$TOTAL_CHURN_EVENTS PacketIns expected"
echo "[Churn] Peak rate   : ~${NUM_PAIRS} PacketIns/sec"
echo ""

# Snapshot Ryu log before churn for N3 isolation
CHURN_LOG_START=0
if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
    CHURN_LOG_START="$(wc -l < "$RYU_LOG" | tr -d " \n")"
fi

FLOWS_BEFORE_CHURN="$(count_total_flows)"
T_CHURN_START="$(date +%s%3N)"

# Start iperf servers on destination hosts
for i in $(seq 0 $((NUM_PAIRS - 1))); do
    dst="${PAIRS_DST[$i]}"
    mnexec -a "${HOST_PIDS[$dst]}" bash -lc \
        "iperf -s 2>/dev/null &" 2>/dev/null || true
done
sleep 1

# Launch churn clients — each fires CHURN_CONNS short back-to-back connections
# Why 1-second connections:
#   - Short enough to create many new flows per host
#   - Long enough for iperf handshake to complete cleanly
#   - Each reconnect = new src port = new unmatched flow = PacketIn
CHURN_PIDS=()
for i in $(seq 0 $((NUM_PAIRS - 1))); do
    src="${PAIRS_SRC[$i]}"
    dst_real="${HOST_IPS[${PAIRS_DST[$i]}]}"
    mnexec -a "${HOST_PIDS[$src]}" bash -lc "
        for j in \$(seq 1 ${CHURN_CONNS}); do
            dst_ip=\$(python3 ${VIP_LOOKUP_HELPER} ${dst_real} ${VIP_MAPPING} 2>/dev/null || echo ${dst_real})
            iperf -c \${dst_ip} -t ${CHURN_CONN_DUR} 2>/dev/null || true
        done
    " > "${OUTDIR}/churn_client_${src}.txt" 2>&1 &
    CHURN_PIDS+=("$!")
done

echo "[Churn] ${#CHURN_PIDS[@]} churn clients running..."
sleep "$((CHURN_DUR / 2))"
dump_ovs "mid_churn"

for pid in "${CHURN_PIDS[@]}"; do wait "$pid" 2>/dev/null || true; done

T_CHURN_END="$(date +%s%3N)"
ELAPSED_CHURN_MS=$(( T_CHURN_END - T_CHURN_START ))
ELAPSED_CHURN_S="$(echo "scale=3; $ELAPSED_CHURN_MS / 1000" | bc)"

dump_ovs "post_churn"
FLOWS_AFTER_CHURN="$(count_total_flows)"
FLOW_DELTA_CHURN=$(( FLOWS_AFTER_CHURN - FLOWS_BEFORE_CHURN ))
stop_all_iperf

# ── [N1] Flow Setup Rate ──────────────────────────────────────────────────────
N1_LOG="${OUTDIR}/N1_flow_setup_rate.txt"
{
    echo "=== [N1] Flow Setup Rate (RFC 8456 §5.2.1) ==="
    echo "Topology   : $TOPO_LABEL"
    echo "Method     : Connection churn — each reconnect = 1 new OVS flow"
    echo "Pairs      : $NUM_PAIRS"
    echo "Conns/pair : $CHURN_CONNS x ${CHURN_CONN_DUR}s"
    echo ""
    # Use peak (mid-churn) flow count for FSR — post-churn is low because
    # VIP rotation expires old flows, making the delta falsely negative.
    FLOWS_MID_CHURN="$(grep 'TOTAL_FLOWS=' "${OUTDIR}/ovs_mid_churn.txt" \
                       2>/dev/null | tail -1 | cut -d= -f2 || echo 0)"
    FLOW_DELTA_PEAK=$(( FLOWS_MID_CHURN - FLOWS_BEFORE_CHURN ))
    HALF_ELAPSED_S="$(echo "scale=3; $ELAPSED_CHURN_S / 2" | bc)"
    echo "Flows before churn : $FLOWS_BEFORE_CHURN"
    echo "Flows at mid-churn : $FLOWS_MID_CHURN  (peak)"
    echo "Flows after churn  : $FLOWS_AFTER_CHURN"
    echo "New flows at peak  : $FLOW_DELTA_PEAK"
    echo "Elapsed (half)     : ${HALF_ELAPSED_S}s"
    echo ""
    if (( ELAPSED_CHURN_MS > 0 )); then
        FSR="$(echo "scale=2; $FLOW_DELTA_PEAK / $HALF_ELAPSED_S" | bc 2>/dev/null || echo 'N/A')"
        echo "FSR (overall)      : ${FSR} flows/sec"
        echo ""
        echo "INTERPRETATION:"
        echo "  FSR = rate at which the controller installs new forwarding rules."
        echo "  Under MTD, each VIP rotation adds extra PacketIn load on top of"
        echo "  baseline FSR. Compare small/medium/large to show how FSR scales."
        echo "  Sub-linear growth = controller is the bottleneck, not the hosts."
    else
        echo "FSR: timing error (elapsed = 0)"
    fi
} > "$N1_LOG"
cat "$N1_LOG"

# ── [2] §5.1.3 Async Message Processing Rate ─────────────────────────────────
ASYNC_LOG="${OUTDIR}/2_async_rate_summary.txt"
{
    echo "=== RFC 8456 §5.1.3 Async Message Processing Rate ==="
    echo "Topology : $TOPO_LABEL"
    echo "Method   : Connection churn (Model 2)"
    echo ""
    echo "Estimated PacketIn events : ~$TOTAL_CHURN_EVENTS"
    echo "Observed elapsed          : ${ELAPSED_CHURN_S}s"
    if (( ELAPSED_CHURN_MS > 0 )); then
        EST_RATE="$(echo "scale=1; $TOTAL_CHURN_EVENTS / $ELAPSED_CHURN_S" | bc 2>/dev/null || echo 'N/A')"
        echo "Estimated event rate      : ~${EST_RATE} events/sec"
    fi
    echo ""
    if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
        CHURN_NEW_LINES="$(tail -n +$((CHURN_LOG_START + 1)) "$RYU_LOG" 2>/dev/null || true)"
        CHURN_RPPT_COUNT="$(echo "$CHURN_NEW_LINES" | grep -c 'RPPT_MEASURED' 2>/dev/null || echo 0)"
        echo "RPPT events logged during churn: $CHURN_RPPT_COUNT"
        echo "(see N3 for percentile breakdown)"
        echo ""
        QUEUE_WARNS="$(echo "$CHURN_NEW_LINES" | grep -ic 'queue\|drop\|overflow\|saturate' 2>/dev/null || echo 0)"
        echo "Controller saturation warnings : $QUEUE_WARNS"
        [[ "$QUEUE_WARNS" -gt 0 ]] && \
            echo "  *** WARNING: controller may have saturated during churn ***"
    else
        echo "Ryu log not available — event count estimated only."
    fi
} > "$ASYNC_LOG"
cat "$ASYNC_LOG"

# ── [N3] RPPT Under Concurrent Load ──────────────────────────────────────────
N3_LOG="${OUTDIR}/N3_rppt_under_load.txt"
{
    echo "=== [N3] RPPT Under Concurrent Load ==="
    echo "Topology : $TOPO_LABEL"
    echo "Window   : Connection churn phase (${CHURN_DUR}s)"
    echo ""
    if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
        CHURN_LINES="$(tail -n +$((CHURN_LOG_START + 1)) "$RYU_LOG" 2>/dev/null || true)"
        CHURN_RPPT_LINES="$(echo "$CHURN_LINES" | grep 'RPPT_MEASURED' || true)"
        CHURN_RPPT_COUNT="$(echo "$CHURN_RPPT_LINES" | grep -c 'RPPT_MEASURED' 2>/dev/null || echo 0)"

        echo "RPPT events during churn: $CHURN_RPPT_COUNT"
        echo ""
        if [[ "$CHURN_RPPT_COUNT" -gt 0 ]]; then
            CHURN_DATA="${OUTDIR}/N3_rppt_churn_values.txt"
            extract_rppt_values "$CHURN_RPPT_LINES" "$CHURN_DATA"
            echo "RPPT statistics under churn load:"
            compute_stats "$CHURN_DATA"
            echo ""
            echo "Compare to [3] idle RPPT:"
            echo "  p99_under_load >> p99_idle  -> churn exposes a bottleneck"
            echo "  p99_under_load ~= p99_idle  -> controller handles churn cleanly"
        else
            echo "No RPPT events captured during churn."
            echo "Ensure controller logs: RPPT_MEASURED: key=(...) elapsed_ms=X.XXX"
        fi
    else
        echo "Ryu log not available."
    fi
} > "$N3_LOG"
cat "$N3_LOG"

# =============================================================================
# [B] MODEL 1 — TCP THROUGHPUT
# =============================================================================
log_step "[B] TCP Throughput — Model 1 — ${NUM_PAIRS} fixed pairs (${DUR}s)"
refresh_vips
stop_all_iperf
dump_ovs "pre_tcp"

for i in $(seq 0 $((NUM_PAIRS - 1))); do
    dst="${PAIRS_DST[$i]}"
    mnexec -a "${HOST_PIDS[$dst]}" bash -lc "iperf -s -i 1" \
        > "${OUTDIR}/B_tcp_server_${dst}.txt" 2>&1 &
done
sleep 1

TCP_PIDS=()
for i in $(seq 0 $((NUM_PAIRS - 1))); do
    src="${PAIRS_SRC[$i]}"
    dst="${PAIRS_DST[$i]}"
    dst_ip="${HOST_VIPS[$dst]:-${HOST_IPS[$dst]}}"   # connect to VIP
    mnexec -a "${HOST_PIDS[$src]}" bash -lc \
        "iperf -c ${dst_ip} -t ${DUR} -i 1" \
        > "${OUTDIR}/B_tcp_client_${src}_to_${dst}.txt" 2>&1 &
    TCP_PIDS+=("$!")
done

echo "[B] ${#TCP_PIDS[@]} TCP flows for ${DUR}s..."
sleep "$((DUR / 2))"
dump_ovs "mid_tcp"
for pid in "${TCP_PIDS[@]}"; do wait "$pid" 2>/dev/null || true; done
stop_all_iperf
dump_ovs "post_tcp"
echo "[B] Done"

# =============================================================================
# [C] MODEL 1 — TCP SESSION CONTINUITY
# =============================================================================
log_step "[C] TCP Session Continuity — Model 1 — ${LONG_DUR}s across VIP rotations"
refresh_vips
stop_all_iperf
dump_ovs "pre_long_tcp"

for i in $(seq 0 $((NUM_PAIRS - 1))); do
    dst="${PAIRS_DST[$i]}"
    mnexec -a "${HOST_PIDS[$dst]}" bash -lc "iperf -s -i 1" \
        > "${OUTDIR}/C_long_tcp_server_${dst}.txt" 2>&1 &
done
sleep 1

LONG_TCP_PIDS=()
for i in $(seq 0 $((NUM_PAIRS - 1))); do
    src="${PAIRS_SRC[$i]}"
    dst="${PAIRS_DST[$i]}"
    dst_ip="${HOST_VIPS[$dst]:-${HOST_IPS[$dst]}}"   # connect to VIP
    mnexec -a "${HOST_PIDS[$src]}" bash -lc \
        "iperf -c ${dst_ip} -t ${LONG_DUR} -i 1" \
        > "${OUTDIR}/C_long_tcp_client_${src}_to_${dst}.txt" 2>&1 &
    LONG_TCP_PIDS+=("$!")
done

echo "[C] ${#LONG_TCP_PIDS[@]} sessions for ${LONG_DUR}s (VIP rotations every 60s)"

for checkpoint in 30 60 90 120 150 180 210 240; do
    [[ "$checkpoint" -lt "$LONG_DUR" ]] && { sleep 30; dump_ovs "long_tcp_${checkpoint}s"; }
done

BROKEN=0
for pid in "${LONG_TCP_PIDS[@]}"; do
    wait "$pid" 2>/dev/null
    code=$?
    [[ "$code" -ne 0 ]] && BROKEN=$((BROKEN + 1))
    echo "$code" >> "${OUTDIR}/C_long_tcp_exitcodes.txt"
done
stop_all_iperf

{
    echo "=== TCP Session Continuity Summary ==="
    echo "Topology         : $TOPO_LABEL"
    echo "Sessions total   : $NUM_PAIRS"
    echo "Sessions broken  : $BROKEN"
    echo "Sessions survived: $((NUM_PAIRS - BROKEN))"
    if [[ "$NUM_PAIRS" -gt 0 ]]; then
        SURVIVAL="$(echo "scale=1; ($((NUM_PAIRS - BROKEN)) * 100) / $NUM_PAIRS" | bc)"
        echo "Survival rate    : ${SURVIVAL}%"
    fi
    [[ "$BROKEN" -eq 0 ]] && \
        echo "RESULT: PASS — all sessions survived VIP rotations" || \
        echo "RESULT: FAIL — $BROKEN session(s) broken by VIP rotation"
} > "${OUTDIR}/C_session_continuity_summary.txt"
cat "${OUTDIR}/C_session_continuity_summary.txt"

# =============================================================================
# [3 + N2] RFC 8456 §5.1.4 — RPPT IDLE + PERCENTILES
#   "Idle" = RPPT events that fired before the churn window started.
#   These come from connection establishment during QoS phases (ping, TCP, UDP).
#   The churn-window RPPT is isolated in N3 above.
# =============================================================================
log_step "[3+N2] RFC 8456 §5.1.4 — RPPT Idle + Percentiles"

RPPT_SUMMARY="${OUTDIR}/3_rppt_summary.txt"
{
    echo "=== RFC 8456 §5.1.4 + [N2] RPPT Idle + Percentiles ==="
    echo "Topology : $TOPO_LABEL"
    echo "Source   : Ryu log ($RYU_LOG)"
    echo ""
    echo "Idle RPPT = events before churn window started (lines ${RYU_LOG_START}-${CHURN_LOG_START})"
    echo "Churn RPPT is isolated in N3_rppt_under_load.txt"
    echo ""
    if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
        _ryu_start=$(( RYU_LOG_START + 1 ))
        _churn_end=$(( CHURN_LOG_START ))
        if [[ "$_churn_end" -gt "$_ryu_start" ]]; then
            IDLE_LINES="$(sed -n "${_ryu_start},${_churn_end}p" \
                          "$RYU_LOG" 2>/dev/null || true)"
        else
            IDLE_LINES="$(tail -n +${_ryu_start} "$RYU_LOG" 2>/dev/null || true)"
        fi

        IDLE_RPPT_LINES="$(echo "$IDLE_LINES" | grep 'RPPT_MEASURED' || true)"
        IDLE_COUNT="$(echo "$IDLE_RPPT_LINES" | grep -c 'RPPT_MEASURED' 2>/dev/null || echo 0)"

        echo "Idle RPPT events: $IDLE_COUNT"
        echo ""
        if [[ "$IDLE_COUNT" -gt 0 ]]; then
            IDLE_DATA="${OUTDIR}/3_rppt_idle_values.txt"
            extract_rppt_values "$IDLE_RPPT_LINES" "$IDLE_DATA"
            echo "Idle RPPT statistics (mean +/- std +/- 95% CI + percentiles):"
            compute_stats "$IDLE_DATA"
        else
            echo "No idle RPPT events found."
            echo "Ensure controller logs: RPPT_MEASURED: key=(...) elapsed_ms=X.XXX"
        fi
    else
        echo "Ryu log not available."
    fi
} > "$RPPT_SUMMARY"
cat "$RPPT_SUMMARY"

# =============================================================================
# [4] RFC 8456 §5.2.3 — FORWARDING TABLE CAPACITY
# =============================================================================
log_step "[4] RFC 8456 §5.2.3 — Forwarding Table Capacity"

{
    echo "=== RFC 8456 §5.2.3 Forwarding Table Capacity ==="
    echo "Topology : $TOPO_LABEL"
    echo "Timestamp: $(date -Ins)"
    echo ""
    ALL_BRIDGES="$(ovs-vsctl list-br 2>/dev/null || true)"
    GRAND_TOTAL=0
    for sw in $ALL_BRIDGES; do
        count="$(ovs-ofctl -O OpenFlow13 dump-flows "$sw" 2>/dev/null \
                 | grep -c 'n_packets' 2>/dev/null || echo 0)"
        echo "  $sw : $count flow entries"
        GRAND_TOTAL=$((GRAND_TOTAL + count))
    done
    echo ""
    echo "  Total across all switches: $GRAND_TOTAL"
    echo ""
    echo "Timeline snapshots:"
    for f in "${OUTDIR}"/ovs_*.txt; do
        tag="$(basename "$f" .txt | sed 's/ovs_//')"
        total="$(grep 'TOTAL_FLOWS=' "$f" 2>/dev/null | tail -1 | cut -d= -f2 || echo 0)"
        echo "  $tag : $total flows"
    done
    echo ""
    PEAK="$(grep 'TOTAL_FLOWS=' "${OUTDIR}"/ovs_*.txt 2>/dev/null | \
            awk -F'=' '{print $NF}' | sort -n | tail -1 || echo 0)"
    echo "  Peak flow count this run: $PEAK"
} > "${OUTDIR}/4_forwarding_table_capacity.txt"
cat "${OUTDIR}/4_forwarding_table_capacity.txt"

# =============================================================================
# [5] RFC 8456 §5.4.2 — NETWORK RE-PROVISIONING TIME
# =============================================================================
log_step "[5] RFC 8456 §5.4.2 — Network Re-provisioning Time"
refresh_vips
stop_all_iperf

src_nrt="${PAIRS_SRC[0]}"
dst_nrt="${PAIRS_DST[0]}"
dst_ip_nrt="${HOST_VIPS[$dst_nrt]:-${HOST_IPS[$dst_nrt]}}"   # connect to VIP

mnexec -a "${HOST_PIDS[$dst_nrt]}" bash -lc "iperf -s -i 1" \
    > "${OUTDIR}/5_nrt_server.txt" 2>&1 &
sleep 1
mnexec -a "${HOST_PIDS[$src_nrt]}" bash -lc \
    "iperf -c ${dst_ip_nrt} -t $((DUR + 60)) -i 1" \
    > "${OUTDIR}/5_nrt_client.txt" 2>&1 &
NRT_PID="$!"

sleep 10
dump_ovs "pre_link_failure"

ALL_BRIDGES="$(ovs-vsctl list-br 2>/dev/null || true)"
FIRST_LEAF="" FIRST_SPINE=""
# industrytp.py uses edge*/agg*/core* naming
for br in $ALL_BRIDGES; do [[ "$br" == edge* ]] && { FIRST_LEAF="$br"; break; }; done
for br in $ALL_BRIDGES; do [[ "$br" == agg* || "$br" == core* ]] && { FIRST_SPINE="$br"; break; }; done

NRT_LOG="${OUTDIR}/5_nrt_timing.txt"
{
    echo "=== RFC 8456 §5.4.2 Network Re-provisioning Time ==="
    echo "Topology    : $TOPO_LABEL"
    echo "Leaf switch : ${FIRST_LEAF:-not found}"
    echo "Spine switch: ${FIRST_SPINE:-not found}"
    echo ""
} > "$NRT_LOG"

FAIL_PORT=""
if [[ -n "$FIRST_LEAF" && -n "$FIRST_SPINE" ]]; then
    # Try matching spine name in port description
    FAIL_PORT="$(ovs-ofctl -O OpenFlow13 show "$FIRST_LEAF" 2>/dev/null | \
                 grep -i "$FIRST_SPINE" | head -1 | \
                 grep -oP '\(\K[^)]+' | head -1 || true)"
    # Fallback: use the highest-numbered port (uplink to aggregation)
    if [[ -z "$FAIL_PORT" ]]; then
        FAIL_PORT="$(ovs-ofctl -O OpenFlow13 show "$FIRST_LEAF" 2>/dev/null | \
                     grep -oP '\(\K[^)]+' | grep -v "^${FIRST_LEAF}" | \
                     sort -t- -k2 -n | tail -1 || true)"
    fi
fi

FAIL_TIME="$(date -Ins)"
echo "link_failure_time=$FAIL_TIME" >> "$NRT_LOG"

if [[ -n "$FAIL_PORT" && -n "$FIRST_LEAF" ]]; then
    ovs-ofctl mod-port "$FIRST_LEAF" "$FAIL_PORT" down 2>/dev/null || true
    echo "[5] Link ${FIRST_LEAF}:${FAIL_PORT} DOWN at $FAIL_TIME"
    echo "failed_port=${FIRST_LEAF}:${FAIL_PORT}" >> "$NRT_LOG"
else
    echo "[5] WARN: Could not identify leaf-spine port — skipping link failure"
    echo "failed_port=none" >> "$NRT_LOG"
fi

sleep 5; dump_ovs "post_link_failure"; sleep 10
RESTORE_TIME="$(date -Ins)"
echo "link_restore_time=$RESTORE_TIME" >> "$NRT_LOG"

[[ -n "$FAIL_PORT" && -n "$FIRST_LEAF" ]] && \
    ovs-ofctl mod-port "$FIRST_LEAF" "$FAIL_PORT" up 2>/dev/null || true

sleep 5; dump_ovs "post_link_restore"

if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
    {
        echo ""
        echo "=== VIP Rotation Events During NRT Window ==="
        tail -n +$((RYU_LOG_START + 1)) "$RYU_LOG" 2>/dev/null | \
            grep -E 'ROTATE:|BIND:|TOPO_DISCOVERY' | head -20 || \
            echo "No rotation events found in log"
    } >> "$NRT_LOG"
fi

wait "$NRT_PID" 2>/dev/null || true
stop_all_iperf
echo "[5] NRT done"
cat "$NRT_LOG"

# =============================================================================
# [N4] VIP RECLAMATION LAG
# =============================================================================
log_step "[N4] VIP Reclamation Lag"

N4_LOG="${OUTDIR}/N4_vip_reclamation_lag.txt"
{
    echo "=== [N4] VIP Reclamation Lag ==="
    echo "Topology : $TOPO_LABEL"
    echo "Measures : time from session end to VIP removed from NAT table"
    echo "Source   : Ryu log token  VIP_RECLAIMED: vip=X lived_ms=X"
    echo ""
    if [[ -n "$RYU_LOG" && -f "$RYU_LOG" ]]; then
        NEW_LINES="$(tail -n +$((RYU_LOG_START + 1)) "$RYU_LOG" 2>/dev/null || true)"
        RECLAIM_LINES="$(echo "$NEW_LINES" | grep 'VIP_RECLAIMED' || true)"
        RECLAIM_COUNT="$(echo "$RECLAIM_LINES" | grep -c 'VIP_RECLAIMED' 2>/dev/null || echo 0)"
        echo "VIP reclamation events: $RECLAIM_COUNT"
        echo ""
        if [[ "$RECLAIM_COUNT" -gt 0 ]]; then
            RECLAIM_DATA="${OUTDIR}/N4_reclamation_values.txt"
            echo "$RECLAIM_LINES" | grep -oP 'lived_ms=\K[0-9.]+' > "$RECLAIM_DATA" || true
            echo "Reclamation lag statistics:"
            compute_stats "$RECLAIM_DATA"
            echo ""
            echo "INTERPRETATION:"
            echo "  Mean lag = avg time an old VIP occupies NAT table post-session"
            echo "  p99 lag  = worst-case NAT table bloat duration"
            echo "  Healthy  : p99_lag << rotation_interval (60s = 60000 ms)"
        else
            echo "No VIP_RECLAIMED events found."
            echo ""
            echo "Add to your Ryu controller where VIP is removed from NAT table:"
            echo '  self.logger.info("VIP_RECLAIMED: vip=%s lived_ms=%.3f",'
            echo '                   vip, (time.time() - session_end_time) * 1000)'
        fi
    else
        echo "Ryu log not available."
    fi
} > "$N4_LOG"
cat "$N4_LOG"

# =============================================================================
# [F] CONTROLLER OVERHEAD
# =============================================================================
log_step "[F] Controller Overhead — CPU + Memory"

{
    echo "=== Controller CPU + Memory Overhead ==="
    echo "Topology : $TOPO_LABEL"
    echo ""
    if [[ -f "${OUTDIR}/F_controller_pidstat.txt" ]]; then
        awk 'NR>3 && $1!~/^#/ && $NF~/ryu/ {
            sum_cpu+=$8; sum_mem+=$13; n++
            if ($8>max_cpu) max_cpu=$8
        }
        END {
            if (n>0) {
                printf "  Average CPU : %.2f%%\n", sum_cpu/n
                printf "  Max CPU     : %.2f%%\n", max_cpu
                printf "  Average RSS : %.0f kB\n", sum_mem/n
            } else { print "  No data parsed from pidstat" }
        }' "${OUTDIR}/F_controller_pidstat.txt"
        echo ""
        echo "Full pidstat log: F_controller_pidstat.txt"
    else
        echo "pidstat not available — install sysstat"
    fi
} > "${OUTDIR}/F_controller_overhead_summary.txt"
cat "${OUTDIR}/F_controller_overhead_summary.txt"
[[ -n "$PIDSTAT_PID" ]] && kill "$PIDSTAT_PID" 2>/dev/null || true

# =============================================================================
# [N5] SCALABILITY SNAPSHOT
#   A structured per-topology summary designed to be read side-by-side
#   across small/medium/large runs to tell the scalability story.
# =============================================================================
log_step "[N5] Scalability Snapshot"
dump_ovs "final"

N5_LOG="${OUTDIR}/N5_scalability_snapshot.txt"
{
    echo "=== [N5] Scalability Snapshot ==="
    echo "Topology   : $TOPO_LABEL"
    echo "Hosts      : $FOUND"
    echo "Pairs      : $NUM_PAIRS"
    echo "Timestamp  : $(date -Ins)"
    echo ""

    PEAK_FLOWS="$(grep 'TOTAL_FLOWS=' "${OUTDIR}"/ovs_*.txt 2>/dev/null | \
                  awk -F'=' '{print $NF}' | sort -n | tail -1 || echo 'N/A')"
    FINAL_FLOWS="$(grep 'TOTAL_FLOWS=' "${OUTDIR}/ovs_final.txt" \
                   2>/dev/null | tail -1 | cut -d= -f2 || echo 'N/A')"
    echo "Flow table peak    : $PEAK_FLOWS entries"
    echo "Flow table final   : $FINAL_FLOWS entries"
    echo ""

    grep 'FSR (overall)' "$N1_LOG" 2>/dev/null || echo "FSR: see N1_flow_setup_rate.txt"
    echo ""

    echo "RPPT idle (p50 / p95 / p99):"
    grep -E 'p50|p95|p99' "$RPPT_SUMMARY" 2>/dev/null | sed 's/^/  /' \
        || echo "  see 3_rppt_summary.txt"
    echo ""

    echo "RPPT under churn load (p50 / p95 / p99):"
    grep -E 'p50|p95|p99' "$N3_LOG" 2>/dev/null | sed 's/^/  /' \
        || echo "  see N3_rppt_under_load.txt"
    echo ""

    grep -E 'RESULT|Survival' "${OUTDIR}/C_session_continuity_summary.txt" \
        2>/dev/null | sed 's/^/Session continuity: /' \
        || echo "Session continuity: see C summary"
    echo ""

    grep -E 'Average CPU|Average RSS' \
        "${OUTDIR}/F_controller_overhead_summary.txt" 2>/dev/null | \
        sed 's/^/Controller: /' || echo "Controller: see F summary"

    echo ""
    echo "────────────────────────────────────────────────────────"
    echo "CROSS-TOPOLOGY COMPARISON (run for all three, then compare):"
    echo ""
    echo "  Metric              small  medium  large  -> Expected trend"
    echo "  FSR (flows/sec)     ?      ?       ?      -> sub-linear growth"
    echo "  RPPT p99 (ms)       ?      ?       ?      -> should stay bounded"
    echo "  Peak flow table     ?      ?       ?      -> linear with hosts"
    echo "  Session survival    ?      ?       ?      -> 100% at all scales"
    echo "  Controller CPU      ?      ?       ?      -> no spike at large"
    echo ""
    echo "Replace ? with values from each topology's N5_scalability_snapshot.txt"
} > "$N5_LOG"
cat "$N5_LOG"

# =============================================================================
# MASTER SUMMARY
# =============================================================================
log_step "BENCHMARK COMPLETE — Master Summary"

SUMMARY="${OUTDIR}/SUMMARY.txt"
{
    cat << EOF
╔══════════════════════════════════════════════════════════════════╗
║         CPAM MTD NSDI Benchmark v3 — Master Summary              ║
╠══════════════════════════════════════════════════════════════════╣
║  Label      : ${LABEL}
║  Topology   : ${TOPO_LABEL}
║  Timestamp  : ${TS}
║  Hosts      : ${FOUND}   Pairs: ${NUM_PAIRS}
║  Duration   : ${DUR}s QoS / ${LONG_DUR}s long TCP / ${CHURN_DUR}s churn
║  Ryu log    : ${RYU_LOG:-not used}
╠══════════════════════════════════════════════════════════════════╣
║  FILE INDEX
╠══════════════════════════════════════════════════════════════════╣
║  [1]    Topology Discovery (§5.1.1)  : 1_topology_discovery_time.txt
║  [2]    Async Msg Rate    (§5.1.3)   : 2_async_rate_summary.txt
║  [3+N2] RPPT + Percentiles(§5.1.4)  : 3_rppt_summary.txt
║  [4]    Forwarding Table  (§5.2.3)   : 4_forwarding_table_capacity.txt
║  [5]    NRT               (§5.4.2)   : 5_nrt_timing.txt
║  [A]    ICMP Latency                 : A_latency_summary.txt
║  [B]    TCP Throughput               : B_tcp_client_*.txt
║  [C]    TCP Session Continuity       : C_session_continuity_summary.txt
║  [D+E]  UDP Jitter + Loss            : DE_udp_summary.txt
║  [F]    Controller CPU + Memory      : F_controller_overhead_summary.txt
║  [N1]   Flow Setup Rate              : N1_flow_setup_rate.txt
║  [N3]   RPPT Under Churn Load        : N3_rppt_under_load.txt
║  [N4]   VIP Reclamation Lag          : N4_vip_reclamation_lag.txt
║  [N5]   Scalability Snapshot         : N5_scalability_snapshot.txt
╠══════════════════════════════════════════════════════════════════╣
║  QUICK RESULTS
╠══════════════════════════════════════════════════════════════════╣
EOF

    echo "║  TOPOLOGY: $TOPO_LABEL"
    echo "║    Hosts=$FOUND  Pairs=$NUM_PAIRS"

    echo "║"
    echo "║  LATENCY:"
    grep 'Topology mean RTT' "${OUTDIR}/A_latency_summary.txt" \
        2>/dev/null | sed 's/^/║    /' || echo "║    see A_latency_summary.txt"

    echo "║"
    echo "║  TCP SESSION CONTINUITY:"
    grep -E 'RESULT|Survival' "${OUTDIR}/C_session_continuity_summary.txt" \
        2>/dev/null | sed 's/^/║    /'

    echo "║"
    echo "║  RPPT IDLE (p50/p95/p99):"
    grep -E 'p50|p95|p99' "$RPPT_SUMMARY" 2>/dev/null | sed 's/^/║    /'

    echo "║"
    echo "║  RPPT UNDER CHURN LOAD (p50/p95/p99):"
    grep -E 'p50|p95|p99' "$N3_LOG" 2>/dev/null | sed 's/^/║    /'

    echo "║"
    echo "║  FLOW SETUP RATE:"
    grep 'FSR (overall)' "$N1_LOG" 2>/dev/null | sed 's/^/║    /'

    echo "║"
    echo "║  VIP RECLAMATION LAG (p99):"
    grep 'p99' "$N4_LOG" 2>/dev/null | sed 's/^/║    /'

    echo "║"
    echo "║  CONTROLLER OVERHEAD:"
    grep -E 'Average CPU|Average RSS' \
        "${OUTDIR}/F_controller_overhead_summary.txt" \
        2>/dev/null | sed 's/^/║    /'

    cat << EOF
╠══════════════════════════════════════════════════════════════════╣
║  10-RUN LOOP COMMAND (RFC 8456 §4.7)                             ║
║                                                                  ║
║  for TOPO in small medium large; do                              ║
║    for i in {1..10}; do                                         ║
║      sudo ./benchmark_nsdi.sh ${DUR} mtd_\${TOPO}_iter\${i} \\      ║
║           ${RYU_LOG:-/var/log/ryu.log} \${TOPO}                          ║
║    done                                                          ║
║  done                                                            ║
║                                                                  ║
║  CONTROLLER LOG TOKENS REQUIRED:                                 ║
║    RPPT_MEASURED: key=(...) elapsed_ms=X.XXX   -> N2, N3        ║
║    VIP_RECLAIMED: vip=X.X.X.X lived_ms=X.XXX  -> N4            ║
╚══════════════════════════════════════════════════════════════════╝
EOF
} > "$SUMMARY"

cat "$SUMMARY"
echo ""
echo "[DONE] All results in: $OUTDIR"
