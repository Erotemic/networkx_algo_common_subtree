# Reuse related child matchings in 2016 isomorphism

Source follows `cdfaff9`. Python 3.13.2, Rust 1.95.0, Linux shared VM.
Normal wheel SHA256:
`c17c8c0ed955244d386bd6ac238dfa7b3c926da7895eb28217afd944ce36fe9c`.

The f64 core now computes an optimum and all right-vertex deletions. It covers
the smaller side using zero-profit dummy columns, retains Hungarian duals and
assignments, and repairs each deleted positive matched vertex with one
augmentation. Unmatched deletions reuse the base witness. Larger-side deletions
project a column; smaller-side deletions replace the removed row with a
zero-cost row on the old occupied columns. A surviving optimum exists on those
columns: an alternating component reaching an old unused column cannot improve
the old optimum and cannot contain the deleted row. Pairs retain original indices.

For nonempty sides, k=min(left,right), l=max(left,right), dense family arithmetic
is O(k²l), scratch is linear, and returned storage is O(k²+right). This is an
algorithm argument, not a new Lean theorem. 2016 nonroot left subtrees reuse
these families when the right degree is at least four. The fixed global left
root and smaller degrees retain single-instance matching. The 2018 schedule
and source-proved exact-integer matching cores are unchanged. Full per-state
graph witnesses and hash tables still prevent a published full-runtime claim.

## Independent correctness

All **44 graph Rust tests pass**. Independent partial-injection enumeration
checks 31,250 exhaustive 2×3/3×2 matrices and their 78,125 deletion members,
plus 2,304 seeded matrices through 5×5 with signed, fractional, zero and forbidden
entries. Checks include optima, injection, original indices, positive selected
weights, rescoring, tiny weights beside large weights, determinism and errors.

Two public graph regressions force each repair orientation in a globally
optimal witness. One also compares the exhaustive Python oracle; both attain
an independent node/edge upper bound and pass public witness rescoring.
The normal installed wheel passes **163 tests, zero skips**, with compiled
parity mandatory where supported. The identical Rust-only ABI3 wheel passes
163 tests on each CPython 3.10–3.14; strict audit reports zero violations or
version mismatches. No Lean claim is added about f64 arithmetic, graphs or FFI.

## Measurements

The [kernel artifact](2026-11-14-matching-families.jsonl) retains seven samples
after two warmups, including witnesses and induced-matrix copies:

| Matrix | Uniform speedup | Signed/optional speedup |
| --- | ---: | ---: |
| 8×8 | 2.01× | 1.25× |
| 16×16 | 3.10× | 1.49× |
| 32×32 | 5.79× | 6.05× |
| 4×64 | 29.26× | 36.98× |
| 64×4 | 5.12× | 6.60× |
| 1×256 | 54.43× | 47.54× |
| 256×1 | 0.56× | 0.58× |

The last row is a regression; graph integration bypasses families at that
right degree. Microsecond measurements have appreciable noise.

Installed APIs include conversion, bindings and original-node/path witnesses.
[Before](2026-11-14-family-before.json) and
[after](2026-11-14-family-after.json) each retain 228 rows, five samples after
one warmup, measured sequentially without concurrent builds. Objectives agree
and every public witness is independently rescored outside the timed region.
New double-star and chain-versus-star cases exercise nonroot high degrees.

| 2016 API workload | Before seconds | After seconds | Speedup |
| --- | ---: | ---: | ---: |
| Chain 32/32 | 0.001053 | 0.001021 | 1.03× |
| Star 32/32 | 0.000647 | 0.000663 | 0.98× |
| Balanced 32/32 | 0.000967 | 0.001040 | 0.93× |
| Random 32/32 | 0.000973 | 0.000887 | 1.10× |
| Double-star 32/32 | 0.001136 | 0.000671 | 1.69× |
| Chain versus star 32/32 | 0.001710 | 0.000624 | 2.74× |
| Identical module tree 166/166 | 0.007780 | 0.009024 | 0.86× |
| Wrapped module tree 166/214 | 0.007043 | 0.009156 | 0.77× |
| ResNet50/101 166/319 | 0.015189 | 0.014494 | 1.05× |

The module regressions remain an optimization task: eager parent-family caching
does unnecessary work, and repaired rooted witnesses still copy descendants.
Kernel speedups do not establish universal API speedups. The 2018 medians on
the same 32/32 shapes remain within 0.95–1.05× of baseline. Whole-process RSS
is 172→176 MB, including Python and all workloads. Separate
[allocation counts](2026-11-14-graph-allocation-family.jsonl) retain requested
bytes/calls and instrumented runtimes with the limitations in the
[earlier report](2026-11-14-graph-shared-witness.md).

```bash
cargo test --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml
cargo bench --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench matching_families
cargo bench --locked --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench graph_allocations
# Outside the checkout, with the chosen Release wheel installed:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --module-trees --repeat 5 --warmup 1 --json results.json
```
