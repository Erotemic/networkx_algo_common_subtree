# Current implementation capabilities

Inspected 2026-11-14, incorporating the parity overlay, the compiled Cython
empty-input fix, and graph/matching Python integration. This matrix distinguishes exposed production
APIs from standalone Rust/Lean implementations. Update it with implementation
milestones; full verification remains a final verified-release requirement.

| Algorithm / mode | Usable Python API / default | Implementations and independent checks | Performance and verification boundary |
| --- | --- | --- | --- |
| Ordered embedding, equality/custom affinity | `maximum_common_ordered_subtree_embedding`, `balanced_embedding.longest_common_balanced_embedding`; `auto` prefers legacy Rust, then Cython, then Python | Python iterative/recursive, Cython, memoized/interned PyO3 Rust; exhaustive pair-deletion oracle and differential tests | Installed balanced API: legacy Rust median 4.43x/3.25x over Python/Cython for equality, 3.87x/3.12x for fractional affinities. Production affinity implementation not source verified |
| Ordered embedding, unweighted | Same APIs with `node_affinity=None`; opt-in `impl="verified-rust"` | Also actual verified flat-token Rust core, original-index token readback and graph adapter tests | Lean proves core optimum, witnesses, parser, memo bounds and guided reconstruction. Installed API verified backend is 6.99x slower than legacy Rust at median (1.28–137x range); it remains opt-in. Full production runtime proof open |
| Ordered isomorphism, equality/custom/unweighted | `maximum_common_ordered_subtree_isomorphism`, `balanced_isomorphism.longest_common_balanced_isomorphism`; same `auto` policy | Python iterative/recursive, Cython, legacy PyO3 Rust; independent original-parent subset enumeration checks adjacency-preserving forest feasibility and optima | Single-label exhaustive cases, multicolor equality and fractional original-node affinity comparisons pass. Verified structural reference Rust core exists but original-index verified Python backend is missing |
| Droschinsky 2016 weighted unordered isomorphism | Public `maximum_common_subtree_isomorphism`; `auto` selects Rust, Python exhaustive fallback | Existing Rust DP bound through PyO3; signed/fractional scalar or callback weights, optional label equality, empty/nonempty objectives, original-node/path witnesses and independent rescorer | Installed API/raw-binding benchmark covers chains, stars, balanced/random and asymmetric trees. Mathematical recurrence proofs exist; graph Rust refinement and published optimized matching runtime remain open |
| Droschinsky 2018 distance-penalized embedding | Public `largest_weight_common_subtree_embedding_with_distance_penalty`; same backends/options | Existing Rust DP; independent subset/bijection/path oracle and public witness rescoring | Long paths receive only skipped-vertex penalties; edge reward/compatibility applies only when both paths have one edge. Both Rust/Python corrected in `d188b67`; public regression retained. Installed API benchmark exists; optimized schedule/runtime and graph Rust refinement remain open |
| Weighted matching, floating point | Standalone Rust API only | `common_subtree_algorithms::max_weight_bipartite_matching`, exhaustive injection tests | Used internally by graph DP. Signed optional weights; f64 arithmetic, not an exact-integer proof |
| Exact assignment / partial matching | Public `min_cost_assignment` / `max_weight_partial_matching`, Rust required | `verified_assignment_core`; signed i64, checked i128, forbidden edges, public dual certificates; independent permutation/injection tests and integer-boundary cases | Actual total-correctness Lean endpoints prove optimum and exact indices/weight. PyO3/Python conversion remains tested, not source proved |
| Exact sparse augmentation / deletion repair | Standalone Rust only | Actual one-path augmentation verified; compact deletion caller implemented, 546 induced-instance tests | Caller projection/refinement still open. Full-matrix cut scans; published optimized sparse queue/runtime not implemented |

## Executed baseline

Python 3.13.2, Rust 1.95.0; both Cython extensions and PyO3 built with CMake
Release. `COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1 python -m pytest -q`
passes **97 tests** (one skip; all required native backends execute); the six overlay differential tests
execute Python, Cython, legacy Rust and unweighted verified Rust as applicable.
The initial run exposed `StopIteration` on empty Cython inputs; both actual
Cython implementations now handle typed empty inputs correctly.

All Rust baselines passed: **39 graph-crate tests**, **8 ordered-core tests**,
and **15 exact-assignment tests**. The PyO3 crate builds/tests but currently has
no Rust unit tests; its behavior is exercised through Python. The maintained
Lean library passes **3,713 jobs**, and both existing Lean example suites pass.
No new end-of-formalization axiom audit was run.

A CPython 3.13 Linux wheel containing Rust and both Cython extensions was built
and installed under `/tmp/common-subtree-software-baseline-install`; the full
test directory passes from outside the checkout with mandatory native parity.
This wheel is not ABI3. Existing measurements are under
`dev/benchmarks/`: graph reference, owned ordered memoization and guided
indexed witnesses. They are different workloads and do not establish a
Cython/legacy/verified Rust speed ratio. The overlay benchmark now supports
explicit affinity modes, required backend availability and strict score
agreement. Installed-API comparisons, wider scaling/allocation evidence and
ABI3 validation remain pending.

## Python graph/matching integration milestone

A fresh Release wheel with both Cython extensions and all Rust families passes
**130 tests, zero skips** from outside the checkout with mandatory native
backends. This includes 30 graph API tests, 36 seeded signed/fractional labeled
tree pairs against independent exhaustive objectives, original-vertex/path
validation, the 2018 long-path discriminator and overflow rejection without
aborting Python. Three exact-matching tests enumerate 48 square assignment
matrices and 100 rectangular partial-matching matrices independently, check
dual certificates, exact i64 extrema/i128 totals and failure behavior. Wheel CI
now runs the full test directory with required compiled backends.

The installed graph API benchmark records 144 measurements, five repeats each,
including raw PyO3 calls on identical inputs. On 32/32 stars the existing graph
reference takes 0.295 s (2016) and 0.360 s (2018); ordinary balanced trees take
0.00381/0.00698 s. This is an observed high-degree bottleneck. Small four-vertex
Rust APIs are 3.5–20.3x faster than exhaustive Python on these workloads; this
does not compare against a polynomial Python DP. See the reproducible commands
and limitations in [the benchmark report](../../dev/benchmarks/2026-11-14-unordered-python-apis.md).

Ordered parity now uses an independent subset oracle for isomorphism as well
as pair-deletion enumeration for embedding. Parent adjacency and a shared
original parent for forest roots are checked explicitly. Eighty fractional
affinity cases per algorithm use unique token indices mapped to distinct
original objects; original witness feasibility and rescoring are checked.
These tests exposed and fixed Cython embedding's string-only token locals and
f32 affinity/score storage. Tuple integer tokens and valid f64 precision/range
now work. The expanded strict source suite passes **138 tests, zero skips**;
all required compiled backend tests execute.

Rectangular matching removes dummy rows/columns, temporary cost/profit matrices
and per-augmentation buffer allocations in the f64 graph core. The fresh
installed wheel passes **139 tests, zero skips**, including arbitrary signed
and forbidden callback-table parity. All **41 graph Rust tests** pass, including
31,250 exhaustive rectangular matrices. The same 32/32 star workload improves
to 0.110 s (2016, **2.68x**) and 0.163 s (2018, **2.20x**); other measured shapes
improve 1.18–1.72x. See [the report](../../dev/benchmarks/2026-11-14-unordered-rectangular.md).
The exact integer verified cores are unchanged. Specialized paper matching,
optimized graph schedules and their production source proofs remain open.

The 2016 solver now roots the left tree once and enumerates each highest
retained vertex and arbitrary right image. All existing exhaustive/native and
139 installed-wheel tests pass. The same 32/32 star drops from 0.110 s to
0.000879 s (**125x**); ResNet-sized public APIs improve **3.63–6.04x**.
The 2018 solver is unchanged by this rooting optimization. API/raw/native
measurements and process-wide RSS are in [the report](../../dev/benchmarks/2026-11-14-unordered-fixed-root.md).
This does not close the paper's specialized matching or production proof work.

## Immediate implementation queue

Installed ordered balanced-API comparisons now cover both algorithms, equality,
fractional affinity, and unweighted modes over chains, stars, balanced/random,
asymmetric and adversarial shapes. Seven-repeat measurements and required
backend/score gates are in [the report](../../dev/benchmarks/2026-11-14-ordered-python-apis.md).
The verified backend's measured slowdown prevents a default switch. NetworkX
conversion overhead, larger realistic cases and allocations still need wider
coverage.

1. Complete ordered variants and intended
   affinity extensions, including verified isomorphism witness exposure.
2. Extend independent oracles and strict compiled-backend CI; fix whichever
   backend disagrees with the mathematical optimum.
3. Benchmark installed APIs and optimize measured bottlenecks/paper schedules,
   starting with unnecessary padded matching work on high-degree inputs.
4. Stabilize packaging/defaults, then finish production proofs and the final
   verified release obligations. Cython remains available during migration.
