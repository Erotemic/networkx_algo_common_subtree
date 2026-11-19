# Root the left 2016 input once, 2026-11-14

Source follows `8312fd8`. A connected adjacency-preserving selected subtree
has a unique highest vertex in any fixed rooting of the left tree. Enumerating
that vertex and its arbitrary right image covers every solution. The solver
now fixes the left orientation once, choosing a maximum-degree root, and keeps
the existing matching recurrence, signed objective and witness logic. This
avoids many redundant high-degree matching subproblems. Edge scoring is
undirected: simultaneous reversal of mapped endpoints preserves its value.

The 2018 algorithm is unchanged. For topological embeddings, the highest
vertex of the selected path hull can be skipped, so the same shortcut alone
would omit valid cross-branch paths. Its optimized path-combination schedule
and the 2016 specialized all-deletion matching machinery remain open.

Release wheel SHA256:
`6c446c593681dee701fcd041a49b97bc260afa593c27fa0a73370bde01d67f35`.
Python 3.13.2, Rust 1.95.0, same shared VM as prior reports. Five repeats and
one warmup, complete installed public APIs and raw PyO3 calls. All witnesses
are independently rescored outside timing. The installed wheel passes **139
tests, zero skips**, with compiled backends mandatory; all **41 graph Rust
tests** pass, including exhaustive Prüfer-tree/injection cases. No new Lean
source-refinement or complexity claim is made.

| 2016 workload | Before seconds | After seconds | Speedup |
| --- | ---: | ---: | ---: |
| Chain, 32/32 | 0.002662 | 0.001164 | 2.29x |
| Star, 32/32 | 0.110089 | 0.000879 | 125.20x |
| Balanced, 32/32 | 0.003220 | 0.001126 | 2.86x |
| Random, 32/32 | 0.003027 | 0.001175 | 2.58x |
| ResNet50 identical, 166/166 | 0.048946 | 0.008486 | 5.77x |
| Wrapped convolutions, 166/214 | 0.038456 | 0.010602 | 3.63x |
| ResNet50 vs ResNet101, 166/319 | 0.110210 | 0.018240 | 6.04x |

The 2018 ResNet-sized times are 0.270/0.302/0.618 s, within 4% of the
preceding wheel. This is control-run noise, not an embedding optimization.
The 2016 star improvement from the initial public-API baseline (0.295 s) is
335x across the two optimizations. Larger and mixed-label high-degree cases
still require measurement before generalizing that result.

Artifacts: [full new API/raw run](2026-11-14-unordered-fixed-root.json),
[preceding wheel's identical module fixtures](2026-11-14-unordered-module-baseline.json),
[native Rust measurements](2026-11-14-fixed-root-native.jsonl).
The two process-wide RSS high-water marks are 269/271 MiB, respectively;
they include Python, input fixtures, all solvers and rescorers, and do not
establish a per-solver memory improvement. Raw PyO3 times exclude NetworkX
conversion; the native benchmark excludes Python altogether.

```bash
# In each installed-wheel environment, from outside the checkout:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --sizes 4,8,16,32 --repeat 5 --warmup 1 --module-trees --json results.json
# To measure only module fixtures in the preceding environment:
python /path/to/checkout/dev/bench_unordered_apis.py \
  --sizes '' --repeat 5 --warmup 1 --module-trees --json module-baseline.json
# Internal Rust, in the checkout:
COMMON_SUBTREE_BENCH_REPEAT=5 COMMON_SUBTREE_BENCH_WARMUP=1 \
COMMON_SUBTREE_BENCH_FORMAT=jsonl cargo bench --locked \
  --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml \
  --bench pytorch_sized_trees
```
