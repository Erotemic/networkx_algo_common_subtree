# Dense oriented-state table for 2016 isomorphism

Source follows `62e864b`; Python 3.13.2, Rust 1.95.0, shared Linux VM.
Normal wheel SHA256:
`37e50049810939dc52ada998f0e87a71899c326ae29f3cb76ea71f4512790c29`.

2016 memoization now uses the fixed left orientation and the right tree's
3m−2 oriented views: a whole view per vertex and one view per excluded neighbor.
A flat table distinguishes uncomputed, incompatible and computed-witness
entries. Sorted adjacency locates a parent view and edge label by binary search;
the default scorer no longer scans an entire high-degree adjacency list for
every edge-pair query. The 2018 memo schedule is unchanged.

All **44 native graph tests** and **165 normal installed-wheel tests pass**,
including mandatory compiled parity. Two new public cases reverse input edge
orders with signed/forbidden callback tables. Independent exhaustive optima,
original edge-table indices and witness rescoring agree. Existing Prüfer-tree,
signed objective, deletion-family and path tests remain passing. No new Lean
source correspondence or complexity theorem is claimed. The identical ABI3
wheel also passes 165 tests on each CPython 3.10–3.14 with strict ABI auditing
clean.

## Operation-count argument and limits

For n,m≥2, let a(u) count children in the fixed left orientation and b(v) be
the right degree. Then Σa=n−1 and Σb=2(m−1). For each nonroot left u and right
v with b≥4, the full matrix and all its right-parent deletions are computed
once. Their matching arithmetic costs
O(a*b*min(a,b)) by the right-deletion family bound. At b≤3, separately solving
each parent view adds only a constant factor. The single global left root
needs only whole-right views. Summing gives
O(n*m*min(Δleft,Δright)) matching arithmetic.

The number of child-pair queries and view accesses is O(n*m). Sorted parent
and edge-label searches cost O(log(max(Δleft,Δright))) per query. Dense table
allocation is O(n*m); retained root/child choices total O(n*m), since the
per-family child-ID storage is bounded by O(min(a,b)²+b), hence O(a*b+b).
Final reconstruction visits only the returned mapping. Its sorting cost is
bounded by O(n*m). Adjacency sorting is also within the total bound.

Thus this implementation has an operation-count argument matching the 2016
target O(n*m*(min(Δleft,Δright)+log(max(Δleft,Δright)))), under unit-cost checked
f64 arithmetic and the stated scoring-query costs. This argument is **not a
Lean proof**, an exact-real numerical guarantee, or a wall-clock guarantee.
Custom `Scoring` implementations add their actual query cost. Python callbacks
are precomputed, so their own running time is additional. Singleton and empty
inputs follow separate constant/linear input-handling paths. Source refinement,
numeric correspondence and formal time/space bounds remain release obligations.

## Measured behavior

[All 228 installed rows](2026-11-14-unordered-dense.json) retain five samples
after one warmup, compared with
[choice-storage baseline](2026-11-14-unordered-choice.json). All objectives
agree and all public witnesses are independently rescored outside timing.

| Workload | 2016 seconds | Speedup |
| --- | ---: | ---: |
| Chain 32/32 | 0.000474 | 1.39× |
| Star 32/32 | 0.000238 | 1.81× |
| Balanced 32/32 | 0.000486 | 1.50× |
| Random 32/32 | 0.000394 | 1.82× |
| Double-star 32/32 | 0.000275 | 1.79× |
| Chain versus star 32/32 | 0.000282 | 1.68× |
| Identical 166/166 | 0.002572 | 2.75× |
| Wrapped 166/214 | 0.002537 | 2.99× |
| ResNet50/101 166/319 | 0.004390 | 2.74× |

The earlier matching-family module regressions are removed. The unchanged
2018 state schedule is within 0.95–1.07× of baseline on these cases, including
shared-VM noise and the changed edge lookup. Whole-process RSS is 119→120 MB,
including Python and all algorithms. This does not isolate 2016 table memory.

Native [allocation counters](2026-11-14-graph-allocation-dense.jsonl) versus
[the preceding implementation](2026-11-14-graph-allocation-choice.jsonl):

| 2016 workload | Requested MB before → after | Peak extra MB before → after |
| --- | ---: | ---: |
| Identical 166/166 | 9.67 → 5.22 | 5.26 → 2.77 |
| Wrapped 166/214 | 15.72 → 5.43 | 10.34 → 3.27 |
| ResNet50/101 166/319 | 19.37 → 10.33 | 10.51 → 5.38 |
| Chain64 | 5.73 → 4.42 | 1.59 → 1.04 |

These are requested heap bytes, excluding input setup and allocator overhead,
not RSS. Dense storage can reserve more unused entries for incompatible inputs;
the asymptotic memory limit is explicit rather than dependent on hash occupancy.

The [larger scaling run](2026-11-14-isomorphism-dense-scaling.json) records 96
public/raw rows, seven samples after two warmups. Public medians in seconds:

| Equal input sizes | Chain | Star | Double-star | Chain versus star |
| --- | ---: | ---: | ---: | ---: |
| 64 | 0.002120 | 0.001009 | 0.001186 | 0.000838 |
| 128 | 0.005935 | 0.005132 | 0.007124 | 0.003137 |
| 256 | 0.025501 | 0.032561 | 0.052286 | 0.013645 |
| 512 | 0.112562 | 0.237022 | 0.369071 | 0.059205 |

Chains and chain-versus-star are roughly quadratic across the larger sizes;
the high-degree matching workloads grow faster, as the degree factor permits.
This empirical agreement does not prove asymptotic complexity.

```bash
# Outside the checkout, using the installed Release wheel:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --module-trees --repeat 5 --warmup 1 --json results.json
python /path/to/checkout/dev/bench_unordered_apis.py --algorithm isomorphism \
  --sizes 64,128,256,512 --repeat 7 --warmup 2 --json scaling.json
```
