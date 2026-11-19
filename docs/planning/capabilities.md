# Current implementation capabilities

Release priority, 2026-11-19: prepare **0.3.0**, selected by the user. Both
unordered families already have public Python and native Rust endpoints.
The README now documents their installation, weights, roots, witnesses and
selection. Standard wheels contain fast Rust; optional compiled Lean delivery
remains available separately. Further verification/optimization research is
deferred and is not a gate for this package release.

The release candidate is checked from a filtered source archive, including
native Rust/Cython and portable Rust-only ABI3 Linux wheels. The same portable
artifact passes **234 tests, 10 optional Lean skips** on each CPython 3.10–3.14;
the minimum NetworkX dependency is now **2.8.8**. The normal installed wheel
passes the same suite with required Rust/Cython parity. All **82 standalone
Rust tests** pass. Public unordered benchmarks include independent witness
rescoring and small exhaustive references. See the
[release evidence](../../dev/packaging/2026-11-19-release-0.3.0.json) and
[remaining release steps](release_0_3_0.md). These checks do not establish new
Lean endpoints or a complete optimized-kernel proof.

The dated implementation and research records below remain historical evidence.

Priority update, 2026-11-18: the active product milestone is efficient ordered
Python APIs with source-connected Lean functional correctness, prioritizing
exact integer affinities and an exact rational/integer proof model. Performance
will be measured; running-time proofs are deferred. See the task-level budgets
and frontier in [README.md](README.md#active-priority-efficient-python-apis-with-functional-correctness).
The implementation/performance matrix below remains historical evidence; the
current fast ordered affinity path uses `f64`, including for Python integer
weights. The new, separate `verified-lean` mode below supplies exact rational/
integer execution without identifying that float path with exact arithmetic.

Current delivery, 2026-11-18: `verified-lean` exposes a compiled, proved
hash-memoized ordered isomorphism algorithm, both root policies, exact
`int`/`Fraction` weights, exact `Fraction` scores and original-input witnesses.
The 4,366-job library, seven Lean cases and 244 installed tests pass after score/
hash/equality/conversion optimization. Median paired-case speedup is 2.79×;
the current small dyadic Lean/Rust latency ratio is 4.23× (1.87--8.56× range).
Both remain selectable; larger rooted chains still expose dense-input overhead.
[Optimization measurements](../../dev/benchmarks/2026-11-18-rational-optimization.md).
[Proof, installed-wheel and benchmark evidence](../../dev/benchmarks/2026-11-18-verified-rational-ordered.md).

Delivery policy: keep verified and optimized/empirically tested implementations
selectable from Python. A documented speed penalty is acceptable for a verified
mode; benchmark both through installed public APIs against the same applicable
references. Explicit verified selection must enforce its assurance domain and
must not silently fall back to unverified code. `auto` alone conveys no proof
guarantee. See [backend policy](backend_parity_and_cython_retirement.md).

Proof-only follow-up, 2026-11-16: the [reified lookup operational pilot](lean-complexity-campaign/evidence/lookup-source-pilot.md)
now has checked instruction accounting and universal value/event contracts
inside its declared read-only model. The 3,750-job library and four Lean
example suites pass. Its reifier/reference interpretation remain trusted;
production Rust runtime, backend selection and wheel evidence are unchanged.

Inspected 2026-11-14, incorporating the parity overlay, the compiled Cython
empty-input fix, and graph/matching Python integration. This matrix distinguishes exposed production
APIs from standalone Rust/Lean implementations. Update it with implementation
milestones; a future fully verified release has additional proof gates beyond
the ordinary 0.3.0 package release.

| Algorithm / mode | Usable Python API / default | Implementations and independent checks | Performance and verification boundary |
| --- | --- | --- | --- |
| Ordered isomorphism, exact rational, both root policies | Both public ordered isomorphism APIs, explicit `impl="verified-lean"`; optional native executable bundled with `BUILD_LEAN_BACKEND=ON` | Directly compiled Lean hash-memoized solver with cached exact scores and collision-safe fast hashing/equality; unchanged full witness/score/identity theorem statements; 98 weighted input/policy oracle combinations and full 244-test installed suite | Exact unbounded integer/rational arithmetic; conversion/transport tested. Small dyadic median latency ratios: 4.23× Rust, 2.05× Cython, 1.77× Python after 2.79× paired-case speedup. Expanded median 3.77× Rust, but large rooted chain 32.45×; sparse affinity delivery is a clear frontier. Optimized Rust proof remains separate; `auto` unchanged |
| Ordered embedding, equality/custom affinity | `maximum_common_ordered_subtree_embedding`, `balanced_embedding.longest_common_balanced_embedding`; `auto` prefers legacy Rust, then Cython, then Python | Python iterative/recursive, Cython, memoized/interned PyO3 Rust; exhaustive pair-deletion oracle and differential tests | Installed balanced API: legacy Rust median 4.43x/3.25x over Python/Cython for equality, 3.87x/3.12x for fractional affinities. Production affinity implementation not source verified |
| Ordered embedding, unweighted | Same APIs with `node_affinity=None`; opt-in `impl="verified-rust"` | Also actual verified flat-token Rust core, original-index token readback and graph adapter tests | Lean proves core optimum, witnesses, parser, memo bounds and guided reconstruction. Installed API verified backend is 6.99x slower than legacy Rust at median (1.28–137x range); it remains opt-in. Full production runtime proof open |
| Ordered isomorphism, equality/custom/unweighted | `maximum_common_ordered_subtree_isomorphism`, `balanced_isomorphism.longest_common_balanced_isomorphism`; same `auto` policy | Python iterative/recursive, Cython, legacy PyO3 Rust; independent original-parent subset enumeration checks adjacency-preserving forest feasibility and optima | Production Rust memoizes scores/choices and reconstructs once: general cases improved 2.42–2.44× in a short installed check. Original-identity affinity mathematical optima are proved for both policies. Local source append/readback bridges are proved conditionally; full production DP/memo/state/score refinement remains open. The source-proved structural core stays opt-in as unweighted `reference-rust`; its complete indexed/token reference path is source proved and it is exponential |
| Root-preserving ordered isomorphism | Both isomorphism APIs accept `rooted=True`; same backends/default | Rust now computes only the level recurrence; 529 exhaustive small pairs, 80 fractional original-index cases, graph root retention and independent rescoring | The choice/level-only change improves rooted Rust 3.35–3.88× over its previous implementation in a short installed check. Existing unweighted root-pruning math/source reference is distinct from this weighted production implementation; its refinement remains open |
| Droschinsky 2016 weighted unordered isomorphism | Public `maximum_common_subtree_isomorphism`; `auto` selects Rust, Python exhaustive fallback | Dense oriented-state Rust DP through PyO3; signed/fractional scalar or callback weights, optional label equality, empty/nonempty objectives, original-node/path witnesses and independent rescorer | Dense oriented-state DP, fixed-left rooting and matching deletion families have independent checks and a written operation-count argument for the 2016 target. Graph Rust refinement and formal optimized runtime remain open |
| Droschinsky 2018 distance-penalized embedding | Public `largest_weight_common_subtree_embedding_with_distance_penalty`; same backends/options | Fixed-left matching families and rerooted skip DP; finite nonnegative or infinite penalty; independent subset/bijection/path oracle and public witness rescoring | Long paths receive only skipped-vertex penalties; edge reward/compatibility applies only when both paths have one edge. Both Rust/Python corrected in `d188b67`; public regression retained. Fixed-left matching families, rerooted skips and distinct-branch joins are implemented/tested. Installed module cases improve 19–36×; Constant-time view/branch lookup is implemented; formal runtime and graph Rust refinement remain open |
| Rooted graph objectives, both families | Both APIs accept `roots=(u,v)` for ambient orientations and `root_to_root=True` to require the supplied pair | Rust `RootConstraint`, independent subset/bijection/path root predicates, direct NetworkX witness checks, original-node rescorers; signed and forbidden weights retained | All 50 native and 228 installed tests pass, including high-degree repair under each policy. Rooted specs/recurrences exist in Lean; production algorithm/root/Python refinement remains open; IEEE-754 correctness is outside the initial proof scope. Rooted/forced module API and callback costs are measured separately |
| Weighted matching, floating point | Standalone Rust API only | `common_subtree_algorithms::max_weight_bipartite_matching` and all-right-deletion families, exhaustive injection tests | Used internally by graph DP. The occupied-column transposed repair now has a conditional ordered-ring optimality proof and independent partial-matching reduction; actual source/warm-invariant and runtime refinement remain open. f64 execution is not an exact-integer proof |
| Exact assignment / partial matching | Public `min_cost_assignment` / `max_weight_partial_matching`, Rust required | `verified_assignment_core`; signed i64, checked i128, forbidden edges, public dual certificates; independent permutation/injection tests and integer-boundary cases | Actual total-correctness Lean endpoints prove optimum and exact indices/weight, including the new no-positive early return. PyO3/Python conversion remains tested, not source proved |
| Exact right-deletion matching family | Public `max_weight_partial_matching_deletions`, Rust required | Existing source-proved `verified_assignment_core::deletion`; original and all right-deleted optima with original indices; 859 exhaustive objective comparisons plus rectangular/boundary cases | Reference family recomputes affected cases. Installed three-sample comparison spans 0.81–2.62× over separate single calls; sparse repair integration remains open. [Evidence](../../dev/benchmarks/2026-11-14-exact-matching-families.md) |
| Exact sparse augmentation / deletion repair | Standalone Rust only | Actual one-path augmentation verified; compact deletion caller implemented, 546 induced-instance tests | Complete exact reference caller proved under the copied-graph numeric input invariant, including projections, repair, original indices and duals; original family integration open. Full-matrix cut scans; published optimized sparse queue/runtime not implemented |

## Current executed validation

Validated algorithm/proof source: **`1555b645d9196f5497c9c1c50b4da22f9d5da098`**.
Fresh source-only normal Rust+Cython and portable CP310 ABI3 manylinux_2_28 x86_64
wheels each pass **234 installed tests, zero skips**. Normal parity requires
compiled Rust/Cython; ABI3 checks all nine Rust entries and Cython absence.
The identical portable wheel passes on glibc 2.28 and each CPython **3.10–3.14**;
strict stable-ABI auditing finds no violations or version mismatches.
[Exact hashes and runtime evidence](../../dev/packaging/2026-11-14-manylinux.json)
are under `indexed_isomorphism_stopping_point`.

All **50 graph**, **13 ordered-core**, **19 exact-assignment** Rust tests,
**3,743 Lean jobs**, both existing Lean example suites and pinned extraction
`--check` pass. Independent contraction/recurrence enumeration covers 197 trees
and 19,503 unordered Dyck pairs. The [printed Definition 2 counterexample](lozano_valiente_2004_containment_definition_audit.md)
remains documented; the operational recurrence has zero mismatches.

The subsequent `a4280b2` changes only oracle-job dependency installation.
Its complete 44-test command passes in a fresh environment. The earlier
[remote PR run](https://github.com/Erotemic/networkx_algo_common_subtree/actions/runs/43651015446)
passed Lean, Rust, normal wheels, ABI3 and five runtime jobs; the oracle job
failed before collection because `xdoctest` was absent, now fixed locally.
A remote run of these new commits is still outstanding. The final checkpoint
commit is documentation/evidence only; no new timing campaign was run.

| Assurance boundary | Established | Still required for the final verified release |
| --- | --- | --- |
| Unweighted ordered references | Mathematical optima; actual Rust embedding and rooted/general isomorphism through original-index/token APIs | Python/PyO3 vertex conversion; production optimized algorithms and bounds |
| Affinity ordered isomorphism | Independent original-identity optima for both policies; conditional actual append/materializer correspondence | Actual optimized DP/memo feasibility, scores and witness provenance |
| Production ordered embedding | Usable optimized Rust/Cython/Python, independent objective and witness checks | Production source refinement including affinity extensions and complete bounds |
| Exact matching | Actual total-correctness proofs for assignment, partial matching and reference deletion family | Optimized family integration, applicable resource bounds and binding correspondence |
| Droschinsky 2016/2018 | Independent graph/path specifications, mathematical recurrence proofs, usable optimized Rust APIs and exhaustive checks | Production source/schedule and witness refinement; formal time/space bounds |
| Distribution | Fresh normal and ABI3 Linux builds, installed tests, stable-ABI audit | Current-revision remote CI, remaining platforms and final reproducibility requirements |

The production floating graph crate remains outside the current extraction
boundary; its integer-only uniform-index constructor is source proved.
IEEE-754 correctness is deliberately excluded from the initial proof scope;
[arithmetic boundary](README.md#initial-proof-scope-arithmetic-boundary).
These are partially verified development artifacts. No production defaults
changed; Cython remains available. The precise proof endpoints and resume
commands are in [PROOF_STATUS.md](../../proofs/PROOF_STATUS.md).

## Measured implementation evidence

- **Production ordered isomorphism** now caches scores/choices and reconstructs
  only the winner, with a dedicated level-only rooted computation. General
  Rust improves 2.42–2.44× and rooted Rust 3.35–3.88× in a three-sample installed
  check of equality/fractional modes. One 128-pair star observation lowers
  whole-process peak RSS 71,292→43,604 KiB. All 234 required-native API tests,
  13 ordered-core tests and existing Lean proofs pass; actual optimized
  score/choice/reconstruction refinement remains open.
  [Measurements and assurance boundary](../../dev/benchmarks/2026-11-14-ordered-iso-choices.md).
  The subsequent actual materializer theorem closes token emission/termination
  under valid arena/root/output bounds, with DP feasibility/optimality and
  resource refinement still open. The cursor-stack change has one small timing
  check. [Source milestone](../../dev/benchmarks/2026-11-14-iso-choice-stack.md).
  The actual production append now also has a source contract: stable old
  references, exact new forest assembly and coordinate preservation through
  emission. The score DP is unchanged; no new timing campaign was run.

- **Exact matching with no positive edge** now returns an independently maximum
  empty witness before square construction, with the actual-source total proof
  preserved. The installed family improves 1.85–2.97× on nonpositive 4×4/8×8
  cases and 1.39–2.32× on zero-column inputs in one three-sample check. Positive
  cases remain noisy (0.78–1.06×); no general speedup is claimed.
  [Evidence and remaining sparse-family work](../../dev/benchmarks/2026-11-14-exact-nonpositive.md).

- **Uniform complete child matchings** use direct cardinality-optimal witnesses,
  including all right deletions; other matrices retain Hungarian matching.
  Native uniform32 families improve 23.4×; installed star512 APIs improve
  3.30×/3.90× for 2016/2018. All 50 native and 228 normal-wheel tests pass.
  Exact ordered-ring diagonal and complete deletion-family optimality/witnesses
  are now proved. The production integer constructor now has source-refinement,
  index/uniqueness and live-vector-count proofs. Pair-storage/tree degree sums
  remain model-level; full caller, allocation and runtime refinement are open.
  [Source milestone and short regression check](../../dev/benchmarks/2026-11-14-uniform-source.md). [Evidence](../../dev/benchmarks/2026-11-14-uniform-matching.md).

- **Structural isomorphism reference** now runs from both Python interfaces,
  with original token/vertex witnesses and rooted/general modes. Independent
  subset oracles cover 1,058 exhaustive pairs and 160 original-index cases.
  On eight-pair stars it is 625× slower than optimized Rust, so it stays opt-in.
  Both reconstruction policies and the complete indexed/token Rust entry points
  now have total source-correctness proofs, including original indices, optima
  and input-error handling. Python/PyO3 conversion remains tested, not proved.
  [Evidence](../../dev/benchmarks/2026-11-14-ordered-isomorphism-reference.md).

- **Infinite distance penalties** now forbid skipped vertices in both backends
  and both witness validators, for every root policy. The native case uses the
  optimized 2016 solver; 144 independently enumerated signed/forbidden cases
  agree with isomorphism. Seven-repeat API/raw measurements cover 684 rows.
  [Evidence](../../dev/benchmarks/2026-11-14-infinite-penalty.md).

- **Rooted graph APIs** now expose ambient and forced-root objectives for both
  Droschinsky families, with original vertices and all existing scoring modes.
  Independent root/path oracles pass; the current suite has 50/228 native/installed tests. Default
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
  and two byte-identical fresh builds with the same source timestamp. The later
  `e272d36` rooted-API source-only rebuild passes 199 tests on the glibc floor
  and all five CPython runtimes.
  [Commands/evidence](../packaging.md). CI uses this profile and requires native
  backends; remote execution and macOS/Windows/other architectures remain open.

## Remaining work in priority order

1. Complete optimized/source-verified ordered coverage: indexed isomorphism
   reconstruction, scoring extensions and production implementation refinement.
   Every existing algorithm family now has public Python access; the structural
   isomorphism reference is deliberately restricted to small unweighted inputs.
2. Continue measured optimization, including applicable bounded-integer improvements.
   Preserve independent oracles and default-backend feature/performance gates.
3. Validate portable wheel builds and CI, then finish mathematical/production
   refinement, witnesses, affinity extensions and formal time/space proofs.
4. Complete the final verified-release gates. The f64 graph solvers, optimized
   ordered production code and Python/FFI boundaries are not fully verified.
   Cython stays available during migration; development builds/use can proceed.

The original-identity affinity isomorphism extension now has independent
operational pruning contracts, parent/order/uniqueness proofs and complete
witnessed mathematical optima under both policies. Its production arena
projection closes conditional local feasibility/readback and derives output
size from the smaller original input. Actual weighted DP/memo correspondence,
the separate affinity-embedding extension and full resource/time proofs remain
open. This proof-only milestone changes no runtime behavior or measured target.
