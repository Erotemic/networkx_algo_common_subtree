# Current implementation capabilities

Inspected 2026-11-14 after `fa531e8`, incorporating the parity overlay and the
compiled Cython empty-input fix. This matrix distinguishes exposed production
APIs from standalone Rust/Lean implementations. Update it with implementation
milestones; full verification remains a final verified-release requirement.

| Algorithm / mode | Usable Python API / default | Implementations and independent checks | Performance and verification boundary |
| --- | --- | --- | --- |
| Ordered embedding, equality/custom affinity | `maximum_common_ordered_subtree_embedding`, `balanced_embedding.longest_common_balanced_embedding`; `auto` prefers legacy Rust, then Cython, then Python | Python iterative/recursive, Cython, memoized/interned PyO3 Rust; exhaustive pair-deletion oracle and differential tests | Legacy optimized Rust is exposed. Whole installed-API comparative measurements pending; production affinity implementation not source verified |
| Ordered embedding, unweighted | Same APIs with `node_affinity=None`; opt-in `impl="verified-rust"` | Also actual verified flat-token Rust core, original-index token readback and graph adapter tests | Lean proves core optimum, witnesses, parser, memo bounds and guided reconstruction. Native owned-cache/reference benchmarks exist; it is slower and is not the default. Full production runtime proof open |
| Ordered isomorphism, equality/custom/unweighted | `maximum_common_ordered_subtree_isomorphism`, `balanced_isomorphism.longest_common_balanced_isomorphism`; same `auto` policy | Python iterative/recursive, Cython, legacy PyO3 Rust; current overlay adds parity and necessary witness checks | Independent exhaustive isomorphism oracle still needed. Verified structural reference Rust core exists but original-index verified Python backend is missing |
| Droschinsky 2016 weighted unordered isomorphism | Exhaustive Python oracle in `common_subtree_reference`; Rust DP **not yet bound to Python** | Standalone `common_subtree_algorithms::maximum_common_subtree_isomorphism` and nonempty form; independent connected-subset/bijection oracles | Native graph-reference benchmark exists. Mathematical recurrence proofs exist; production Rust graph DP/refinement and optimized matching runtime remain open |
| Droschinsky 2018 distance-penalized embedding | Exhaustive Python oracle; Rust DP **not yet bound to Python** | Standalone `largest_weight_common_subtree_embedding_with_distance_penalty` and nonempty form; independent path/skeleton scoring | Long paths receive only skipped-vertex penalties; edge reward/compatibility applies only when both paths have one edge. Both Rust/Python corrected in `d188b67`; tests retain discriminators. Optimized schedule/runtime and graph Rust refinement remain open |
| Weighted matching, floating point | Standalone Rust API only | `common_subtree_algorithms::max_weight_bipartite_matching`, exhaustive injection tests | Used internally by graph DP. Signed optional weights; f64 arithmetic, not an exact-integer proof |
| Exact assignment / partial matching | Standalone Rust only | `verified_assignment_core`; signed i64, checked i128, forbidden edges, independent permutation/injection tests | Actual total-correctness Lean endpoints prove optimum and exact indices/weight. Python exposure missing |
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

## Immediate implementation queue

1. Bind both existing Droschinsky Rust families to Python with original-node
   mappings, signed/custom weights, empty/nonempty objectives and independent
   witness rescoring; preserve the corrected 2018 path semantics.
2. Expose reusable exact matching; complete ordered variants and intended
   affinity extensions, including verified isomorphism witness exposure.
3. Extend independent oracles and strict compiled-backend CI; fix whichever
   backend disagrees with the mathematical optimum.
4. Benchmark installed APIs and optimize measured bottlenecks/paper schedules.
5. Stabilize packaging/defaults, then finish production proofs and the final
   verified release obligations. Cython remains available during migration.
