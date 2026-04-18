# Metrics investigation report

## What is missing / not measured

From the generated outputs in `metrics/`, these metrics were not actually measured or are incomplete:

1. **Topology discovery time** (`§5.1.1`) is missing because `TOPO_DISCOVERY_COMPLETE` was not found in the controller log.
2. **RPPT idle and RPPT under churn** (`§5.1.4`, `N2`, `N3`) are missing because no `RPPT_MEASURED` events were found.
3. **VIP reclamation lag** (`N4`) is missing because there is no `N4_vip_reclamation_lag.txt` output and no reclaimed-event summary in the folder.
4. **UDP jitter/loss is mostly unmeasured** (`D+E`) because almost all rows are `N/A`; only one pair has a parsed loss result.
5. **Several summary-indexed artifacts are absent from this folder** (`B`, `C`, `F`, `N4` and prefixed names like `1_`, `2_`, etc.), which suggests this directory is a curated subset and/or files were renamed after generation.

## Why these metrics are missing

### A) Required log tokens are absent in the run output
The benchmark script explicitly depends on these controller log tokens:

- `TOPO_DISCOVERY_COMPLETE ...` for discovery time
- `RPPT_MEASURED ...` for RPPT (idle + churn)
- `VIP_RECLAIMED ...` for reclamation lag

If tokens are absent, the script prints fallback messages and leaves those metrics blank.

### B) Controller/app mismatch is likely
The repository has at least two controller variants:

- `mtd_dns2.py` **does** log `RPPT_MEASURED` and `TOPO_DISCOVERY_COMPLETE`.
- `mmtd_dns.py` has reclaim logs, but does not show the same explicit benchmark token coverage.

If the benchmark was run against a controller that does not emit all required tokens, the missing metrics are expected.

### C) Output-folder filename mismatch
`summary.txt` points to files such as `1_topology_discovery_time.txt`, `2_async_rate_summary.txt`, `N1_flow_setup_rate.txt`, etc.
In this folder those exist without prefixes (for example `topology_discovery_time.txt`, `async_rate_summary.txt`, `flow_setup_rate.txt`). This indicates post-processing/renaming or partial copying.

## How results look (quick quality read)

### Positive signals

- **Scale is realistic**: `504` hosts / `252` pairs in large topology.
- **Flow setup rate** is reported at `538.79 flows/sec` during churn.
- **Session continuity** is reported `100.0%` pass in summary snapshots.
- **Controller overhead** appears low (`~0.23%` average CPU, `~69.5 MB` RSS).

### Risk / concern signals

- **RPPT is completely unobserved** (`0` events), so controller reaction-time claims are unvalidated.
- **Topology discovery time is unobserved** (missing discovery token).
- **UDP quality data is unusable for most pairs** (251/252 rows `N/A`).
- **Latency tails are very high** (many max RTT values >1s, reaching ~1.99s), despite zero packet loss in ICMP summary.
- **Flow-table peak is high** (`11117` entries), which is expected under churn but should be watched for sustained growth.

## Recommended fixes for next run

1. Run benchmark against the controller variant that emits all required tokens (`RPPT_MEASURED`, `TOPO_DISCOVERY_COMPLETE`, `VIP_RECLAIMED`) and confirm in `RYU_LOG` before running full duration.
2. Add a short preflight check in `benchmark_nsdi.sh` to fail early if token patterns are absent after warmup.
3. Keep original benchmark filenames (prefixed) when copying to `metrics/` to preserve index consistency.
4. Re-run UDP test with lower aggregate offered load and verify iperf server-side summary parsing for all destinations.
5. Keep one `cpam_nsdi_*` raw output directory archived alongside the curated `metrics/` subset for traceability.
