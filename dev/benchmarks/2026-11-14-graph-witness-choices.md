# Reconstruct only the winning graph witness

Source follows `4be4789`; Python 3.13.2, Rust 1.95.0, same shared Linux VM.
Normal wheel SHA256:
`a13ad7ed280d37fc4a6bcac0be36f3d22b947ae71d87c65232d199959156fb68`.

Both graph solvers now store constant-size score/choice IDs in memo entries.
Each mapped-root choice stores its original vertex pair and selected child
IDs. These IDs always refer to choices already constructed. Skip states and
unmatched matching deletions reuse an ID, with their own adjusted score.
An iterative traversal expands only the winning witness, then sorts its
original pairs once. It no longer copies, sorts or compares complete mappings
at each rooted state. Public witnesses remain ordinary node/path tuples.
Equal-scoring candidates retain the first traversal choice, preserving the
documented deterministic-per-backend contract; particular tied witnesses can
change. No cross-backend witness identity is required.

All **44 graph Rust tests** and **163 normal installed-wheel tests pass**, with
compiled parity required. Existing independent subset/bijection/path oracles
and rescorers check optimum, injectivity, skipped paths, signed/forbidden
scores and original indices. Seeded public cases repeat calls to check ties.
The identical ABI3 wheel also passes all 163 tests on each CPython 3.10–3.14,
with strict symbol auditing clean. This implementation change adds no Lean
refinement or complexity claim.

## Allocation evidence

The separate allocation executable measures requests, excluding input setup;
these are neither RSS nor allocator overhead. Compare
[matching-family baseline](2026-11-14-graph-allocation-family.jsonl) with
[choice storage](2026-11-14-graph-allocation-choice.jsonl). Decimal MB:

| Workload | Allocation calls before → after | Requested MB before → after | Peak extra MB before → after |
| --- | ---: | ---: | ---: |
| 2018 identical 166/166 | 394,873 → 368,556 | 104.39 → 79.54 | 51.32 → 27.64 |
| 2018 wrapped 166/214 | 394,874 → 368,557 | 117.23 → 92.38 | 57.53 → 34.06 |
| 2018 ResNet50/101 166/319 | 792,745 → 740,215 | 209.97 → 160.69 | 106.17 → 55.37 |
| 2016 chain64 | 105,370 → 92,854 | 9.39 → 5.73 | 5.86 → 1.59 |
| 2018 chain64 | 211,120 → 190,668 | 21.70 → 14.76 | 12.97 → 5.49 |
| 2016 identical 166/166 | 39,672 → 17,507 | 9.26 → 9.67 | 5.51 → 5.26 |

Contiguous choice-pool growth can slightly increase cumulative requested bytes
for shallow isomorphism workloads despite reducing allocation calls and peak.

## Installed API evidence

[All 228 rows](2026-11-14-unordered-choice.json) retain five samples after one
warmup, binary/machine metadata and raw-binding measurements. Comparison is to
[the preceding installed wheel](2026-11-14-family-after.json). All objectives
agree and all public witnesses are independently rescored outside timing.

| Workload | 2016 seconds / speedup | 2018 seconds / speedup |
| --- | ---: | ---: |
| Chain 32/32 | 0.000659 / 1.55× | 0.002358 / 1.36× |
| Star 32/32 | 0.000431 / 1.54× | 0.105758 / 1.17× |
| Balanced 32/32 | 0.000728 / 1.43× | 0.002916 / 1.28× |
| Random 32/32 | 0.000716 / 1.24× | 0.003601 / 1.16× |
| Double-star 32/32 | 0.000493 / 1.36× | 0.023929 / 1.21× |
| Chain versus star 32/32 | 0.000475 / 1.32× | 0.007364 / 1.25× |
| Identical 166/166 | 0.007063 / 1.28× | 0.138054 / 1.33× |
| Wrapped 166/214 | 0.007592 / 1.21× | 0.167457 / 1.23× |
| ResNet50/101 166/319 | 0.012033 / 1.20× | 0.333840 / 1.25× |

Whole-process RSS falls 176→119 MB, including Python, fixtures and all runs.
Shared-VM noise still limits small timing differences. Further work includes
dense state storage, unnecessary eager parent-family states, 2018 optimized
path scheduling, production refinement and complete published runtime proofs.

```bash
cargo bench --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench graph_allocations
# Outside the checkout, using the installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --module-trees --repeat 5 --warmup 1 --json results.json
```
