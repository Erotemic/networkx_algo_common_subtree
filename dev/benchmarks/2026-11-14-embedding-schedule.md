# Fixed-left matching families and rerooted skips for 2018

Source follows `e27d434`; Python 3.13.2, Rust 1.95.0, shared Linux VM.
Normal wheel SHA256:
`ad98c32740f7bc6f333b8e6969395c4887e1c4e5d5a73a34219835b8865c46f1`.

The production 2018 Rust solver now fixes the left orientation and processes
vertices in postorder. At each left vertex it first computes **all mapped
right views**, using the already completed left-child mapped/skipped tables
and one matching deletion family per right vertex. It then computes skipped
views in two passes over the right tree. A downward pass establishes child
messages; a rerooting pass uses the best two incoming branches to produce every
parent exclusion. This separates mapped matching dependencies from same-left
skip dependencies, avoiding circular recursive rerooting.

The final optimum includes both cases from
[the primary paper's Lemma 10](https://drops.dagstuhl.de/storage/00lipics/lipics-vol117-mfcs2018/LIPIcs.MFCS.2018.54/LIPIcs.MFCS.2018.54.pdf):
a retained highest left vertex, and a skipped highest left vertex on one path.
For the latter, each right edge separates two continuations from **distinct**
left child branches. Keeping the two best candidates per side suffices for
the exact cardinality-two choice. The central left skip pays one additional
penalty; no direct-edge reward is added. The winner reconstructs its two
disjoint choice trees once, preserving original vertices and path witnesses.

## Correctness and assurance

All **44 native graph tests** and **172 normal installed Python tests pass**,
with compiled parity mandatory where supported. Native independent injection
enumeration covers small labeled tree shapes, signed weights and penalties.
New public tests force crossing a forbidden highest vertex, prohibit reusing
one left branch twice, force both matching-repair orientations, and compare
twelve signed/forbidden 6×5 high-degree callback problems against independent
subset/bijection/path enumeration. Every returned witness is independently
rescored. Existing empty, negative nonempty, overflow and long-path edge-reward
regressions pass. The identical ABI3 wheel passes 172 tests on each CPython
3.10–3.14, with strict ABI auditing clean.

The matching arithmetic sums to O(n*m*min(Δleft,Δright)); skip and cardinality-two
work has O(n*m) table accesses. Dense score/choice storage is O(n*m). **Current
parent-view and default edge-label searches still cost logarithmic time**, and
adjacency sorting is additional preprocessing. Removing those costs remains
necessary for the precise 2018 O(n*m*minΔ) implementation claim. No new Lean
dichotomy, schedule, witness, source-refinement or complexity theorem is claimed.
The production f64 assurance boundary is unchanged.

## Installed performance

[All 228 API/raw/oracle rows](2026-11-14-unordered-embedding-schedule.json)
retain five samples after one warmup, with machine/binary metadata. Comparison
is to [the all-orientations reference](2026-11-14-unordered-dense.json).
Objectives agree and public witnesses are rescored outside timing.

| 2018 workload | Before seconds | After seconds | Speedup |
| --- | ---: | ---: | ---: |
| Chain 32/32 | 0.002446 | 0.000612 | 4.00× |
| Star 32/32 | 0.098671 | 0.000551 | 179.11× |
| Balanced 32/32 | 0.002921 | 0.000503 | 5.81× |
| Random 32/32 | 0.003388 | 0.000569 | 5.95× |
| Double-star 32/32 | 0.023896 | 0.000443 | 53.90× |
| Chain versus star 32/32 | 0.007789 | 0.000547 | 14.23× |
| Identical 166/166 | 0.144633 | 0.005909 | 24.48× |
| Wrapped 166/214 | 0.171240 | 0.008934 | 19.17× |
| ResNet50/101 166/319 | 0.337074 | 0.009290 | 36.28× |

The 2016 matching/table schedule is retained. Its measured ratios range
0.83–1.23× across these cases, including shared-VM noise and the shared
orientation helper's traversal recording; no 2016 speedup is claimed here.
Whole-process RSS falls **120→53 MB**, including Python, fixtures and all runs.

Native requested-heap counters compare
[before](2026-11-14-graph-allocation-dense.jsonl) and
[after](2026-11-14-graph-allocation-embedding-schedule.jsonl), decimal MB:

| 2018 workload | Allocation calls before → after | Requested MB before → after | Peak extra MB before → after |
| --- | ---: | ---: | ---: |
| Identical 166/166 | 368,556 → 17,181 | 79.54 → 7.81 | 27.64 → 4.45 |
| Wrapped 166/214 | 368,557 → 17,181 | 92.38 → 9.34 | 34.06 → 5.61 |
| ResNet50/101 166/319 | 740,215 → 33,843 | 160.69 → 15.22 | 55.37 → 8.61 |
| Star32 | 86,272 → 2,824 | 35.75 → 0.56 | 1.54 → 0.25 |
| Chain64 | 190,668 → 91,487 | 14.76 → 3.79 | 5.49 → 0.98 |

These are requested bytes excluding input setup, fragmentation and allocator
metadata, not per-solver physical RSS. Instrumented times include counters.

```bash
cargo test --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml
cargo bench --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench graph_allocations
# Outside the checkout, with the installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --module-trees --repeat 5 --warmup 1 --json results.json
```
