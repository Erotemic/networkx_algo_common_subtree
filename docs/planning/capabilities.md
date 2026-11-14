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
| Root-preserving ordered isomorphism | Both isomorphism APIs accept `rooted=True`; same backends/default | Exposes the already-computed level state; 529 exhaustive small pairs, 80 fractional original-index cases, graph root retention and independent rescoring | Installed Rust median 2.16x/1.57x faster than Python/Cython on the rooted weighted suite. Existing unweighted root-pruning math/source reference is distinct from this weighted legacy production implementation; its refinement remains open |
| Droschinsky 2016 weighted unordered isomorphism | Public `maximum_common_subtree_isomorphism`; `auto` selects Rust, Python exhaustive fallback | Dense oriented-state Rust DP through PyO3; signed/fractional scalar or callback weights, optional label equality, empty/nonempty objectives, original-node/path witnesses and independent rescorer | Dense oriented-state DP, fixed-left rooting and matching deletion families have independent checks and a written operation-count argument for the 2016 target. Graph Rust refinement and formal optimized runtime remain open |
| Droschinsky 2018 distance-penalized embedding | Public `largest_weight_common_subtree_embedding_with_distance_penalty`; same backends/options | Fixed-left matching families and rerooted skip DP; independent subset/bijection/path oracle and public witness rescoring | Long paths receive only skipped-vertex penalties; edge reward/compatibility applies only when both paths have one edge. Both Rust/Python corrected in `d188b67`; public regression retained. Fixed-left matching families, rerooted skips and distinct-branch joins are implemented/tested. Installed module cases improve 19–36×; Constant-time view/branch lookup is implemented; formal runtime and graph Rust refinement remain open |
| Rooted graph objectives, both families | Both APIs accept `roots=(u,v)` for ambient orientations and `root_to_root=True` to require the supplied pair | Rust `RootConstraint`, independent subset/bijection/path root predicates, direct NetworkX witness checks, original-node rescorers; signed and forbidden weights retained | All 47 native and 199 installed tests pass, including high-degree repair under each policy. Rooted specs/recurrences exist in Lean; production f64/root/Python refinement remains open. Rooted/forced module API and callback costs are measured separately |
| Weighted matching, floating point | Standalone Rust API only | `common_subtree_algorithms::max_weight_bipartite_matching` and all-right-deletion families, exhaustive injection tests | Used internally by graph DP. Signed optional weights; f64 arithmetic, not an exact-integer proof |
| Exact assignment / partial matching | Public `min_cost_assignment` / `max_weight_partial_matching`, Rust required | `verified_assignment_core`; signed i64, checked i128, forbidden edges, public dual certificates; independent permutation/injection tests and integer-boundary cases | Actual total-correctness Lean endpoints prove optimum and exact indices/weight. PyO3/Python conversion remains tested, not source proved |
| Exact sparse augmentation / deletion repair | Standalone Rust only | Actual one-path augmentation verified; compact deletion caller implemented, 546 induced-instance tests | Caller projection/refinement still open. Full-matrix cut scans; published optimized sparse queue/runtime not implemented |

## Current executed validation

A fresh normal Rust+Cython wheel passes **199 tests, zero skips**, outside the
checkout with compiled parity mandatory. The identical Rust-only CP310 ABI3
wheel passes **199 tests on each CPython 3.10–3.14**, with strict ABI auditing
clean. Independent oracles cover subset/pair deletions, graph bijections/paths,
assignment permutations/injections, original indices, signed/forbidden scores,
root-preserving variants, invalid inputs, overflow and malformed witnesses.
Sphinx HTML builds with warnings treated as errors.

The last executed native suites pass **47 graph**, **8 ordered-core** and
**15 exact-assignment** tests. The last full Lean build passes **3,713 jobs**
and both existing example suites. Mathematical/extracted core source is
unchanged by the subsequent software milestones; the production f64 graph
crate is outside the current extraction boundary. No new end audit was run.

## Measured implementation evidence

- **Rooted graph APIs** now expose ambient and forced-root objectives for both
  Droschinsky families, with original vertices and all existing scoring modes.
  Independent root/path oracles and 47/199 native/installed tests pass. Default
  unrooted median runtime ratios remain 1.006/0.999 against the prior build.
  [Contracts, tests and measurements](../../dev/benchmarks/2026-11-14-graph-root-modes.md).

- **2016** fixes the left root, reuses matching deletion families, stores choice
  IDs and uses dense directed-view tables. Installed module APIs improve
  2.74–2.99× at the dense-table milestone; a 96-row run reaches 512 vertices.
  [Timings, allocations and operation argument](../../dev/benchmarks/2026-11-14-isomorphism-dense.md).
- **2018** uses left postorder mapped tables, two-pass right skip messages and
  both highest-vertex cases, including distinct-branch path joins. This improves
  32/32 stars 179× and module trees 19–36× over the all-orientations reference.
  [Schedule evidence](../../dev/benchmarks/2026-11-14-embedding-schedule.md).
- **Both graph cores** now use direct view IDs and known branch metadata,
  including original edge indices for callback tables. A written core
  O(n*m*minΔ) operation-count argument assumes constant-time scoring; it is not
  a Lean runtime/refinement theorem. Installed scalar/callback and raw binding
  costs are measured separately. [Evidence](../../dev/benchmarks/2026-11-14-directed-view-ids.md).
- **Independent rescoring** validates supplied paths directly, preserves the
  separate exhaustive bare-pair checker, and improves 64-node embedding
  validation 70–342×. The complete 2018 96-row scaling run now reaches 512
  vertices, with witness validation about 5 ms.
  [Evidence and limits](../../dev/benchmarks/2026-11-14-path-rescoring.md).
- **Unused global-root work** is removed from 2018 while retaining the skipped-
  highest path case. Star512 improves **1.182→0.232 s (5.10×)**; double-star512
  improves **1.69×**. All 44 native and 176 installed tests pass.
  [Repeated scaling evidence](../../dev/benchmarks/2026-11-14-embedding-root-matching.md).
- **Ordered APIs** retain all weighted/rooted/native modes and original vertices,
  opaque hashable tokens and full Python Unicode. Installed equality/fractional/
  unweighted comparisons cover Python, Cython, legacy and verified Rust.
  The slower verified embedding remains opt-in.
  [Ordered comparisons](../../dev/benchmarks/2026-11-14-ordered-python-apis.md),
  [rooted modes](../../dev/benchmarks/2026-11-14-ordered-rooted-weighted.md),
  [token contracts](../../dev/benchmarks/2026-11-14-ordered-token-contract.md).
- **Packaging** validates genuine opt-in Rust-only CP310 ABI3 and normal native
  parity. Source-only → sdist → both wheel modes was executed at `3d68c00`.
  Source-only `5e42f17` also produces a genuine manylinux_2_28 x86_64 wheel:
  176 tests on its glibc floor and each CPython 3.10–3.14, clean Linux/ABI audits,
  and two byte-identical fresh builds with the same source timestamp.
  [Commands/evidence](../packaging.md). CI uses this profile and requires native
  backends; remote execution and macOS/Windows/other architectures remain open.

## Remaining work in priority order

1. Finish any remaining intended ordered variants/extensions, notably original-
   index exposure of the existing verified structural isomorphism core.
2. Continue measured optimization, including applicable bounded-integer improvements.
   Preserve independent oracles and default-backend feature/performance gates.
3. Validate portable wheel builds and CI, then finish mathematical/production
   refinement, witnesses, affinity extensions and formal time/space proofs.
4. Complete the final verified-release gates. The f64 graph solvers, optimized
   ordered production code and Python/FFI boundaries are not fully verified.
   Cython stays available during migration; development builds/use can proceed.
