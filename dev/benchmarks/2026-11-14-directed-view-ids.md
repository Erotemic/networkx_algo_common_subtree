# Constant-time directed views and branch scoring

Source follows `23b0e01`; Python 3.13.2, Rust 1.95.0, shared Linux VM.
Normal wheel SHA256:
`0e9640d9065ba056e5467c39487a96bd7057076d1e3990d5cebdbc625587e086`.

Tree construction now assigns whole-vertex and paired directed-edge view IDs
in linear time, preserving input edge order. Each adjacency reference carries
its original undirected edge-list index. Both graph solvers address memo views
directly; no parent binary search or adjacency sorting remains. A scoring hook
receives known branch metadata. Default label scoring compares those labels
directly, and PyO3 callback tables use the original edge indices directly.
Their computational inner loops contain neither Python callbacks nor hash
lookups. Custom Rust scorers retain the original hook as the default and must
keep both hooks' scores consistent; their actual query cost is additional.

The matching-family argument and the 2018 mapped-then-skipped schedule now give
an O(n*m*minΔ) **core operation-count argument** with O(n*m) auxiliary storage
for nontrivial trees and constant-time scoring. Singleton/empty cases have
separate linear input handling. Tree representation construction is linear;
final witness traversal/sorting is within the same total bound. This also
implies the weaker 2016 bound. It is not a Lean complexity proof, an exact-real
f64 guarantee, or a claim that arbitrary user callbacks take constant time.
Python callback tables add O(n*m) callback invocations before solving.

All **44 native graph tests** and **172 installed Python tests pass**, with
compiled parity mandatory. Independent exhaustive matching/path/callback
oracles, original edge-order reversal checks, signed/nonempty cases and
overflow rejection all pass. The identical ABI3 wheel passes 172 tests on each
CPython 3.10–3.14 with strict auditing clean. The new representation, hook and
production kernels remain outside the existing exact-core Lean assurance boundary.

## Installed measurements

[Scalar after](2026-11-14-unordered-view-ids.json) versus
[the preceding schedule](2026-11-14-unordered-embedding-schedule.json): 228 rows
each, five samples after one warmup, including original-node/path witnesses.
All corresponding objectives agree; public witnesses are independently
rescored outside timing.

| 2018 workload | Before seconds | After seconds | Speedup |
| --- | ---: | ---: | ---: |
| Chain 32/32 | 0.000612 | 0.000601 | 1.02× |
| Star 32/32 | 0.000551 | 0.000516 | 1.07× |
| Balanced 32/32 | 0.000503 | 0.000462 | 1.09× |
| Random 32/32 | 0.000569 | 0.000488 | 1.17× |
| Double-star 32/32 | 0.000443 | 0.000378 | 1.17× |
| Chain versus star 32/32 | 0.000547 | 0.000483 | 1.13× |
| Identical 166/166 | 0.005909 | 0.003507 | 1.68× |
| Wrapped 166/214 | 0.008934 | 0.003900 | 2.29× |
| ResNet50/101 166/319 | 0.009290 | 0.008038 | 1.16× |

The benchmark now also materializes fractional callback scoring modes. Public
timings include callback-table preparation on every invocation; raw PyO3 timing
starts from the same precomputed tables. Comparing
[callbacks before](2026-11-14-unordered-callbacks-before.json) and
[after](2026-11-14-unordered-callbacks-after.json), again 228 rows per build:

| 2018 workload | Public before → after seconds | Public speedup | Raw speedup |
| --- | ---: | ---: | ---: |
| Identical 166/166 | 0.017014 → 0.014489 | 1.17× | 1.39× |
| Wrapped 166/214 | 0.020901 → 0.019712 | 1.06× | 1.56× |
| ResNet50/101 166/319 | 0.032290 → 0.026935 | 1.20× | 1.61× |

Callback preparation now dominates much of these public costs. 32/32 callback
chains show a small regression (0.98×); all samples are retained. Shared-VM
noise remains visible, especially in small cases. Native
[allocation counters](2026-11-14-graph-allocation-view-ids.jsonl) show unchanged
2018 allocation-call counts and peak heap; original-edge metadata adds only a
few KB of cumulative requested bytes. Whole-process scalar RSS is 53→56 MB,
including Python and independent validation, not a per-solver peak.

A larger 2018 run exposed a separate public-rescorer bottleneck: enumerating
all selected vertex pairs and repeatedly scanning edges during path searches
took minutes at 512 vertices, outside the timed solver. That run was stopped
and no completed scaling artifact is claimed. Efficient independent validation
of the supplied path witness is the next implementation task.

```bash
# Outside the checkout, using the chosen installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --module-trees --repeat 5 --warmup 1 --json scalar.json
python /path/to/checkout/dev/bench_unordered_apis.py --weights callbacks \
  --module-trees --repeat 5 --warmup 1 --json callbacks.json
cargo bench --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench graph_allocations
```
