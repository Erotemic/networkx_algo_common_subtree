# Optimizing the proved rational ordered backend

The first optimization makes `verified-lean` **2.79× faster at the median of
paired case speedups** (range 1.31--9.60×), while retaining exact rational
arithmetic and the original public Lean theorem statements. On the original
18 small dyadic cases, its median latency ratio against optimized float Rust
falls from a freshly remeasured **7.96× to 4.23×**. The first release's earlier
measurement was 7.60×; these short runs retain ordinary timing variation.

Parity is workload dependent. The closest small case is 1.87× Rust's latency;
the small-case range is 1.87--8.56×. Expanded 64/128-node cases have a 3.77×
median ratio, but the 128-node rooted chain is 32.45×. The latter exposes the
still-dense affinity input path: the adapter computes/transports n*m weights,
whereas rooted chains only need aligned pairs. There is no uniform parity claim.

## Changes and preserved proof

- Memo entries now carry `Scored`: the witness, its cached rational value and
  an erased proof `value = score affinity witness`. Candidate selection compares
  these scalar values; joining two witnesses adds the two cached values and
  the new affinity. `Scored.choose_witness` proves the same exact tie/selection
  behavior as the independent mathematical recurrence. `solveResult_eq` proves
  the complete cached result agrees with the original public score expression.
- Query hashing uses only the first original identity. Equality still compares
  the **complete forest**, so duplicate identities and hash collisions remain
  correct. A checked structural `inputDecEq` uses Lean's standard
  `withPtrEqDecEq` shortcut on shared subtrees. This adds no uniqueness premise
  to the solver's optimum theorem. Repeated-label, colliding-shape cases are
  checked both through Lean and the actual native protocol.
- Python resolves fixed node mappings once, retains canonical `int`/`Fraction`
  values, and checks their numerator signs. It avoids redundant Fraction copies,
  ABC lookups and rational comparisons for each matrix cell. Other Rational
  instances still use the general canonical conversion. Empty-input behavior,
  exact weights, eager affinity semantics, witness rescoring and backend choice
  are retained.

The independent mathematical specification was not edited. Both
`RationalSolver.solveResult_correct` and `solve_unique_endpoints` retain exactly
their prior elaborated `typeExprHash`; neither statement is weakened.
The shared-tool audit covers **72 declarations / 24 theorem declarations**,
using only `propext`, `Classical.choice`, `Quot.sound`. The two-seed statement
closure has **119 records / 458 edges**, no unknown references. Lean proofs
are erased; no proof checking happens during a Python solve. The execution
boundary remains the standard Lean compiler/runtime/library, with independently
tested Python/NetworkX/JSON conversion and transport.

## Installed-API measurements

All measurements run outside the checkout against separately installed old and
new wheels. The baseline is commit `4527c48`, executable SHA-256
`a9c3bb3d9e5bfbc6d1541e42c3707926b517993a18a57d352970f77b8d704066`.
The optimized executable is
`6fec03649ee3e4a61a0fdf4c78b7d3059b77d963d2e9fd7df7687afd1f0b8b1f`.
Both use the identical Rust binary
`ccbeefc62b52f9bbe63d4eb4be81cd5343a288c93c0c0945564cf7ee304473c8`.
The native artifacts and package paths are recorded in every raw file.

The original suite uses 8/16/32-node stars, chains and balanced trees, both root
policies, one warmup and three complete public NetworkX calls per backend/case.
Every measured result is checked against original graph nodes/edges and exact
witness rescoring; all backends' objectives agree. Positive dyadic weights and
small integer weights are exactly representable in f64 for these tests, while
the verified implementation retains general rational execution. Timings include
conversion, affinity callbacks, serialization, IPC, solving and reconstruction.
The timed runs were sequential, with no concurrent build/test processes.

| Workload | Median Lean/Rust latency ratio | Per-case range |
| --- | ---: | ---: |
| 8/16/32 dyadic, original implementation remeasured | 7.96× | 4.42--26.13× |
| 8/16/32 dyadic, optimized | **4.23×** | 1.87--8.56× |
| 8/16/32 integer, optimized | 5.31× | 2.93--8.71× |
| 64/128 dyadic, optimized | 3.77× | 2.70--32.45× |

On the primary dyadic suite, median case latency changes from 8.89 to 3.04 ms.
The optimized backend is 2.05× Cython's median per-case latency (1.21--2.59×),
and 1.77× Python iterative's (0.98--2.26×). Medians of ratios and ratios of
medians need not agree. First-worker-call samples remain about 102--124 ms;
startup was not the target of these optimizations. The native worker's observed
high-water RSS is 82,272 KiB on the primary suite and 88,660 KiB on the expanded
suite (single observations, not memory bounds).

Raw data:

- [fresh baseline](2026-11-18-rational-optimization-baseline.json)
- [optimized dyadic](2026-11-18-rational-optimized.json)
- [optimized integer](2026-11-18-rational-optimized-integer.json)
- [optimized 64/128-node scaling](2026-11-18-rational-optimized-scaling.json)

Diagnostic cProfile observations on three 32-node general-chain solves put the
native/IPC `readline` wait at about 57 ms/call originally, 18 ms after score
caching, and 7 ms after hashing/equality improvements. These are instrumented
diagnostics, not the benchmark results above. Python preparation/callbacks now
account for a large share of that profile. In rooted mode the corresponding
native wait is about 3 ms/call while the adapter still prepares the full matrix.

## Validation and reproduction

The 4,366-job library and 6,272-job native build pass. Seven Lean examples pass,
including the deliberately colliding repeated-label forests. A fresh wheel with
Lean/Rust/Cython installed outside the source tree passes **244 tests, zero
skips**, with both compiled-backend requirement flags enabled. This includes
independent rational subset oracles, exact large-integer/near-tie cases,
concurrent/fork/restart checks and the native collision regression.

Optimized wheel: `networkx_algo_common_subtree-0.2.3-cp313-cp313-linux_x86_64.whl`,
40,693,963 bytes, SHA-256
`a41832161ee2d717640b1d1658f7d736c90b95cd96e4810df6057ccdd332ba02`.
It is under `/var/tmp/subtree-rational-opt-wheels`; installation is
`/var/tmp/subtree-rational-opt-installed`. Cache mounts and the actual CMake
`cargo-target` remain on local ext4. Dependency pins, Rust source, dispatch and
public scoring/root policies are unchanged.

Build/install using [the normal optional-backend commands](../../proofs/VERIFICATION.md).
From `proofs/`, run `lake build`, `lake build verified_ordered` and
`lake env lean Tests/RationalOrderedSolver.lean`. Outside the checkout:

```bash
COMMON_SUBTREE_REQUIRE_LEAN=1 COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1 \
  python -m pytest -q /path/to/checkout/tests
python /path/to/checkout/dev/bench_verified_rational.py --output optimized.json
python /path/to/checkout/dev/bench_verified_rational.py --integer-weights --output integer.json
python /path/to/checkout/dev/bench_verified_rational.py --sizes 64,128 --output scaling.json
```

Local logs/exports use `/var/tmp/subtree-rational-opt-*`, with native intermediate
build logs named `subtree-rational-{score-cache,cheap-hash,equality}-build.log`.
No reliable per-task token counter was available.

## Frontier after this tranche

The largest clear remaining structural issue is dense affinity extraction for
rooted inputs. A sparse/depth-aware or demand-driven interface needs its own
proof that omitted affinities cannot affect feasible optima, plus a compact
transport preserving exact values. A rough initial estimate is 80--250k tokens
/ 1--4 hours, low confidence before an interface/proof spike.

An in-process native Lean interface could remove JSON/IPC and some repeated
conversion. Its source algorithm proof can stay intact, while initialization,
ownership, exact BigInt marshaling, packaging and concurrency require careful
integration tests. Rough initial estimate: 100--300k tokens / 2--6 hours, low
confidence for a Linux-first implementation. These estimates are future budget
choices, not work started or a guarantee of eventual parity. Exact arbitrary-
precision arithmetic and workload shape also affect comparisons with f64.
