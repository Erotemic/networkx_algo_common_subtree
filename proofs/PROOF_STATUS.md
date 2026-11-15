# Common-subtree proof status

## Initial proof scope: IEEE-754 deliberately excluded

Author instruction, 2026-11-14: IEEE-754 correctness is outside the initial
proof scope. Numerical rounding, floating-point stability and overflow
correspondence are not required initial proof endpoints. Existing historical
entries listing floating arithmetic equivalence as open describe an unproved
boundary; they do not override this scope decision.

Mathematical correctness, matching and witness correctness, production
algorithm/schedule correspondence and applicable complexity proofs remain
required. Each correspondence theorem must disclose its arithmetic model and
preconditions. A theorem in exact/abstract ordered arithmetic is not a theorem
about actual `f64` execution. Existing exact integer source proofs keep their
checked-arithmetic safety guarantees. Runtime finite-value, precision and
overflow behavior remains tested independently. No theorem or assumption was
added or changed to implement this scope decision.

## Validated stopping checkpoint: 2026-11-14

The exact validated source is **`1555b645d9196f5497c9c1c50b4da22f9d5da098`**.
Fresh source-only archives contain 595 files and no native libraries. Full Lean
build: **3,743 jobs**, both example suites pass; pinned extraction matches.
Rust suites: **13 ordered**, **19 exact assignment**, **50 graph** tests pass.
The normal Rust+Cython wheel passes **234 installed tests, zero skips**, with
compiled parity mandatory. The portable CP310 ABI3 manylinux_2_28 x86_64 wheel
passes **234 tests, zero skips** on glibc 2.28 and each CPython 3.10–3.14.
All nine native entries are checked; ABI3 contains no Cython library, and strict
ABI auditing finds zero violations/mismatches. Exact source/artifact hashes and
runtime evidence are in the existing [packaging ledger](../dev/packaging/2026-11-14-manylinux.json),
under `indexed_isomorphism_stopping_point`.

The subsequent **`a4280b270075ae8aaf2cb5987a56606e56e5f0df`** changes only CI
oracle dependency installation. Its complete 44-test oracle command passes in
a fresh environment. It changes no algorithm, binding, test or Lean source.
The evidence/checkpoint commit after it changes documentation/JSON only.

Remote CI is no longer uninspected: [run 43651015446](https://github.com/Erotemic/networkx_algo_common_subtree/actions/runs/43651015446)
on the earlier PR head `f9b4afe` / merge `382e29c` passed Lean/extraction, Rust,
normal-wheel, ABI3 build and all five runtime jobs. Its oracle job failed before
collection because `xdoctest` was absent. `a4280b2` fixes that actual failure;
a remote run of the new commits remains outstanding. Local evidence does not
claim a fresh remote success, macOS/Windows artifacts or a fully verified release.

Independent checks again cover 197 ordered trees and **19,503** unordered Dyck
pairs with zero operational-recurrence mismatches. The printed Definition 2
counterexample **`001011 → 0011`** remains established and documented in the
[containment audit](../docs/planning/lozano_valiente_2004_containment_definition_audit.md).
No new benchmark was needed: executable algorithms and backend defaults are
unchanged. Prior small-sample performance evidence remains in `capabilities.md`.

Remaining release blockers are **optimized ordered DP/memo and witness provenance**,
**production Droschinsky 2016/2018 source refinement**, applicable **formal time/space
bounds**, production affinity-extension correspondence, Python/PyO3 conversion
assurance and the remaining distribution/reproducibility/platform work. Exact
matching/reference proofs and conditional production helper proofs do not close
those boundaries. IEEE-754 remains excluded from the initial proof scope.

Resume the maintained local validation from this checkout with:

```bash
set -e
lake -d proofs build
(cd proofs && lake env lean Tests/RootedDynamicProgram.lean && lake env lean Tests/OrderedIsomorphism.lean)
dev/regenerate_rust_lean.sh --check
for crate in verified_ordered_core verified_assignment_core common_subtree_algorithms; do
    cargo test --locked --manifest-path "rust/crates/$crate/Cargo.toml"
done
python -m pip install -r requirements/tests.txt -r requirements/runtime.txt
python proofs/checks/check_tree_contraction_oracle.py
python proofs/checks/check_paper_dp_recurrence.py
```

Build/install the normal wheel and run tests outside the checkout with
`COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1`; use the existing
[packaging commands](../docs/packaging.md) for fresh source archives and the
portable profile. The next proof target is production DP feasibility/optimality
and witness provenance; the generic complexity campaign, sparse-family
integration, default switching and Cython retirement remain deferred.

## Complete original-index/token isomorphism reference path: 2026-11-14

`Rust/IndexedIsomorphismReconstruction` proves total correctness of the actual
rooted and arbitrary-parent reconstruction functions. A success is an independent
whole-subtree pruning with exactly the requested shape and unchanged original
pair identities; rejection proves independent infeasibility. Parent adjacency
is preserved: skipping a child never promotes its grandchildren.

`Paper2004/IndexedIsomorphism` defines independent indexed and token maximum
contracts. `Rust/IndexedIsomorphismEntrypoint.maximum_common_isomorphism_indexed_spec`
composes the source-proved structural optimum, canonical numbering and both
reconstructions. For inputs with fewer than 2^32 pairs it proves source success,
global optimality, exact scores and original-index witnesses for both policies.
`Rust/TokenIsomorphismEntrypoint.maximum_common_token_isomorphism_total_spec`
composes parsing, that indexed solver and actual token emission. Every represented
call terminates: admitted inputs return independently maximum original-token
witnesses; excluded inputs report the correct side, with left-input precedence.
Token indices are increasing, unique, in bounds and read back the common shape.
Internal solver/index errors are unreachable on admitted inputs.

This closes the unweighted **reference** Rust path used by Python's opt-in
`impl="reference-rust"`. Python/PyO3 conversion remains independently tested,
not source proved. The reference is exponential; this does not prove the
optimized default DP, its affinity scores or its time/space bounds. No backend
selection or executable Rust behavior changed. All **3,743 main Lean jobs**,
both existing example suites and pinned extraction `--check` pass.

## Original-identity affinity isomorphism mathematical optima: 2026-11-14

`Paper2004/AnnotatedIsomorphism` independently defines annotated ordered-forest
pruning as the reflexive/transitive closure of whole-child-subtree deletion at
arbitrary contexts. It proves equivalence with structural selection, original
preorder preservation, parent-edge preservation, size bounds and erasure to the
established unlabelled isomorphism contracts. No grandchild promotion is allowed.
General parent regions are specified separately from fixed-parent pruning.

`AffinityIsomorphism` carries pairs of original identities in the witness.
Its projections are independent prunings of both original inputs, with strictly
positive affinity at every selected pair (zero forbids matching). Unique input
identities imply unique witness endpoints. `AffinityIsomorphismDP.level_correct`
and `anywhere_correct` prove complete witnessed optimality against every such
independent candidate over an ordered commutative ring. These are the intended
scoring/isomorphism project extensions, not new statements attributed to the
2004 paper. Mathematical nonpositive pairs are forbidden; existing public
finite/nonnegative input validation is unchanged and not source proved here.

`Rust/IsomorphismAffinityWitness` interprets the actual production arena as this
paired original-endpoint witness. It equates the independent score fold with
the existing abstract affinity fold, proves local source construction preserves
level feasibility from its head/tail invariants, and connects actual emitted
coordinates to both independent projections. For both policies, caller
feasibility derives the source output-size bound from the smaller original
input; no output-size oracle is required beyond that original-input bound.

All **3,739 main Lean jobs** and both existing example suites pass. Six new
kernel-checked examples cover forbidden root affinity, moved-parent recovery,
original identities and zero-affinity exclusion. Rust/Python/generated semantics
are unchanged; the last software validation remains **234 required-native
installed Python tests and 13 ordered-core tests**. No benchmark or extraction
run was repeated for this proof-only milestone.

The actual weighted Rust DP/memo/state representation must still establish the
feasible arena invariant and correspondence to these optimal recurrences.
Production score refinement, conversion, complete resource/time bounds and
the remaining affinity-embedding extension proofs remain open. The new source
readback bridge assumes caller feasibility; it is not an end-to-end optimum
theorem for the optimized Rust backend. IEEE-754 remains deliberately excluded.

## Actual production choice construction and coordinate preservation: 2026-11-14

The optimized ordered-isomorphism solver now calls the integer-only
`append_isomorphism_choice` at its existing append site. Its source operations
remain old-length read, vector push and return of that index; score comparisons,
evaluation order, public APIs and backend selection are unchanged.
`IsomorphismChoiceConstruction.append_isomorphism_choice_spec` proves stable
old-length identity, exact one-entry growth, valid backward links, old-forest
preservation and exact new head/tail forest assembly. The premises are a valid
old arena, old child references and room for one entry. Empty-arena validity
is established separately, and arbitrary suffix extension preserves all old
forest meanings, even without assuming validity of unreachable records.

`append_and_reconstruct_spec` composes actual construction and actual emission,
deriving the new root and forest rather than supplying an output certificate.
`IsomorphismChoiceCoordinates` proves coordinate bounds through both stages:
bounded stored original endpoints produce bounded emitted token indices.
The abstract `affinityScore` fold proves the intended head + tail + root score
equation and preservation of every old mathematical score. This does not identify
actual f64 arithmetic with an additive-monoid model; IEEE-754 stays outside scope.

All **3,735 main Lean jobs**, both example suites, **13 ordered-core Rust** and
**234 required-native installed Python tests** pass. Pinned extraction `--check`
passes. The native head/tail fixture now exercises the actual append helper and
checks that an older witness survives subsequent appends. The fresh normal-wheel
hashes and scope are recorded in the [existing milestone artifact](../dev/benchmarks/2026-11-14-iso-choice-stack-environment.json).
No performance measurement or portable wheel rebuild was repeated for this
inlined source-boundary extraction.

Complete recursive DP/memo invariants, provenance of child choices and original
endpoint bounds from production states, parent/order feasibility, uniqueness,
weighted optimality, Python conversion and runtime/allocation correspondence
remain open. These local constructor/materializer theorems do not certify the
whole optimized backend or arbitrary caller-built forests as valid isomorphisms.

## Actual production ordered-isomorphism materializer proved: 2026-11-14

`Rust.IsomorphismChoices.reconstruct_isomorphism_choices_spec` now proves the
actual production helper safely terminates and emits exactly the independent
arena forest's provided token labels in both inputs, in open/head/close/tail
order. Premises are earlier-child references, a valid optional root and a
representable output size. No source-success/output/optimality oracle is assumed.

`IsomorphismChoiceModel` defines the independent well-founded forest and task
interpretation. `IsomorphismChoiceStack` proves actual active-prefix overwrite,
append and enqueue behavior. `IsomorphismChoiceEmission` proves the actual loop
preserves output/remaining-forest equality, emits one token per side and safely
decreases remaining output length. The public entry point composes initialization
and loop correctness, including the empty arena/root.

The earlier extraction of `Vec::pop` was an unmodeled external, not a source
proof. The actual helper now uses a logical active prefix of reusable vector
slots; regenerated semantics remove that dependency without adding a pop
axiom/specification or changing pins. Existing proofs are preserved.

All **3,732 main Lean jobs**, both example suites, **13 ordered-core Rust** and
**234 required-native installed Python tests** pass. Pinned extraction `--check`
passes. [A single short regression check](../dev/benchmarks/2026-11-14-iso-choice-stack.md)
records timing variance after the stack representation change.

The caller must still be proved to construct a feasible/optimal choice forest
with valid original-input token labels. Weighted score/memo correspondence,
Python conversions and complete resource/runtime refinement remain open. This
helper theorem does not establish parent constraints, uniqueness or optimality
of arbitrary supplied arenas. IEEE-754 remains outside initial scope.

## Production ordered-isomorphism choice reconstruction: 2026-11-14

The weighted optimized Rust backend now memoizes scores/choice IDs and
materializes only the selected original-token witness. Root-preserving calls
evaluate only the level recurrence; general calls separately memoize the
descendant-root recurrence. This aligns the production schedule with the
existing mathematical split without modifying or weakening any theorem.

The actual integer-only `isomorphism_choices` helper is used by PyO3 and included
in pinned maintained Charon/Aeneas semantics. Its full source refinement is
**open**. The weighted production DP/memo/choice correspondence, original-index
witness feasibility and actual resource/runtime proofs remain open as well.
The extraction and existing structural-reference proofs are not an end-to-end
proof of the optimized backend. IEEE-754 remains outside initial proof scope.

All **3,728 main Lean jobs**, both Lean example suites, **13 ordered-core Rust**
and **234 required-native installed Python tests** pass. Pinned regeneration
`--check` passes. Independent parent-preserving subset objectives and fractional
original-index witness checks cover both root contracts; new tests preserve tie
order and exercise invalid/long iterative arena reconstruction. Short installed
measurements show 2.42–2.44× general and 3.35–3.88× rooted median gains, with a
separate 39% lower whole-process peak-RSS observation. [Scope and raw evidence](../dev/benchmarks/2026-11-14-ordered-iso-choices.md).

## Actual exact matching no-positive fast path: 2026-11-14

The production exact single-instance API now returns an empty matching for
nonpositive/forbidden inputs after shape/dimension validation, bypassing the
square assignment construction and solve. `Rust/MatchingNonpositive` proves
both actual scans' termination, checked-index/increment safety and exact
independent sign predicates. `empty_correct` compares the actual empty output
with every valid partial matching, including signed and forbidden weights.
`MatchingEntrypoint.max_weight_partial_matching_total_spec` retains its complete
original specification and now proves the new source branch as well.

All **3,728 main Lean jobs**, both Lean example suites, **19 exact-core Rust**,
**50 graph Rust** and **232 required-native installed Python tests** pass.
Pinned regeneration `--check` passes. Existing matching-family, assignment,
sparse repair and witness proofs survive the regenerated source.
[Three-sample installed measurements](../dev/benchmarks/2026-11-14-exact-nonpositive.md)
record the improvement and positive-case variance. There is no formal runtime
or allocation claim. Actual one-augmentation family integration, the optimized
sparse queue, production tree correspondence and final release gates remain
open. IEEE-754 stays deliberately outside initial proof scope.

## Production transposed-deletion restriction: mathematical justification, 2026-11-14

`Shared/TransposedMatchingDeletion.transposed_repair_global_minimum` justifies
the production family's square repair on the old occupied columns after
zeroing one row. A root-normalized repaired dual extends to every original
column, proving a globally minimum complete injection. Premises are the old
rectangular feasible dual with zero unused-column potentials, the repaired
square feasible/tight certificate and the per-row warm-update bound. No new
global optimum or restricted/unrestricted equivalence is assumed.

`dummyBaseline_spec` and `dummy_initialization` derive the actual mathematical
minimum-baseline initialization and nonroot diagonal tightness.
`warm_rows_adjust` preserves the root/other-row growth invariant for each
nonnegative update containing the root. `Shared/RectangularAssignment` supplies
rectangular weak duality and complementary slackness.
`Shared/RectangularMatchingReduction` connects negative-profit injections to
independently specified maximum partial matchings, including signed/forbidden
weights, positive-pair decoding, original labels and zeroed-row deletion.
The existing partial-bijection extension is reused, rather than assuming an
optimal matching or duplicating the Hungarian recurrence.

All **3,727 main Lean jobs** pass. Rust algorithm bodies and Python APIs stay
fixed; the existing 231-test wheel evidence and short performance measurements
still apply, and no benchmark was repeated for this proof-only change.
Actual production float caller/control-flow refinement, derivation of every
warm invariant from that source, graph schedules and runtime/resource proofs
remain open. These are ordered-ring mathematical theorems; IEEE-754 remains
deliberately outside initial proof scope.

## Exact matching deletion families exposed through Python: 2026-11-14

`max_weight_partial_matching_deletions` now calls the existing actual Rust
`deletion::max_weight_matching_deletions`, whose total correctness is proved by
`Rust.MatchingDeletionEntrypoint.max_weight_matching_deletions_total_spec`.
The public frozen family contains the original optimum and every right-deleted
optimum, with original indices and exact integer totals. This is the reference
recomputation family, not the newly proved sparse one-augmentation integration.

All 231 installed Rust+Cython tests pass, including independent exhaustive
partial-injection objectives and witness rescoring. Nine native entries are
mandatory in CI. Python/PyO3 conversions remain tested, not source proved;
no main core semantics or dependency changes. The last main Lean build remains
3,724 jobs. [Short measurements and boundary](../dev/benchmarks/2026-11-14-exact-matching-families.md)
record the actual installed API. The subsequent source-only `e79b88b` portable
CP310 ABI3 wheel passes 231 tests on glibc 2.28 and all five CPython 3.10–3.14
runtimes, with all nine entries mandatory and strict ABI auditing clean. This
is packaging/conversion evidence, not an additional source proof.

## Complete actual sparse-deletion reference caller: 2026-11-14

`Rust/SparseDeletionEntrypoint.repair_deleted_sparse_vertex_spec` now proves
the actual public Rust caller succeeds from `DeletionReady`: a represented
feasible/tight old permutation, nonpositive optional costs with zero identity
edges, the paper's two-sided numeric envelope/accounting, and zero initial
row/column baselines at the removed vertex. These are old-input conditions;
no new optimum, repair path or source-success certificate is supplied.

`SparseDeletionState.projected_numeric_state` derives the actual projected
feasibility, envelope, exact dual accounting and surviving-dimension bound.
The complete caller then proves both fixed-vertex reuse and nonfixed one-path
augmentation. `CorrectDeletion` includes canonical original vertices, exact
output lengths, original-column witnesses, independent minimum assignment,
feasible tight returned integer duals and the exact repaired-flag meaning.
This covers the exact integer reference caller under its stated input model;
it does not verify the distinct production f64 family or its graph callers.

All **3,724 main Lean jobs**, both Lean example suites, and **18 exact-core
Rust tests** pass. Pinned extraction `--check` reproduces the maintained source
semantics. Six new zero-baseline 4-cycle deletions exercise the intended
initialization regime, forbidden edges, positive repair adjustments and
`i64::MAX` costs against independent induced-permutation optima, alongside
the existing 546 broader deletion cases. Rust algorithm bodies and Python
interfaces are unchanged, so no performance run was repeated.

The original partial-matching copied-graph family still needs source
initialization/construction and integration; the optimized sparse queue and
runtime theorem remain open. Allocation/OOM/resource traces and IEEE-754 are
not asserted by this functional integer-caller theorem. IEEE-754 remains
intentionally outside initial scope.

## Actual sparse-deletion projection, seed and readback: 2026-11-14

The actual Rust row/matrix/potential projection loops now have total source
contracts in `Rust/SparseDeletionProjection`: exact selected contents, safe
reads/increments, termination and projected square shape. Forbidden entries
and signed integer values are preserved, including empty/repeated selections.
`SparseDeletionSeed` and `SparseDeletionReadback` verify the actual checked
bypass-completion and original-column export loops.

`SparseDeletionWarmStart.complete_surviving_permutation_spec` closes the
loop's no-deleted-column premise from the independently defined finite
permutation. It proves exact source correspondence to `compactAssignment`.
`original_columns_permutation_spec` derives all exporter bounds and original
labels from the represented permutation and canonical survivor vector.
`SparseDeletionData` proves exact original finite-coordinate cell/potential
correspondence and transports independent projected minima. The mathematical
`compact_paired_optimum` proves fixed deletions need no repair.

All **3,722 main Lean jobs** and both existing Lean example suites pass.
Production Rust/Python sources and measured targets are unchanged. The last
software validation remains 228 required-native Python, 50 graph Rust and 17
exact-core tests; no new performance run is needed for this proof-only step.

The subsequent complete caller theorem above closes source numeric-state
setup and branch composition. Original partial-matching family integration
and the optimized queue/runtime remain open. This is the exact integer
reference caller; it does not verify the distinct production f64 matching
families or graph schedules. Capacity/OOM/resource traces remain outside these
functional helper contracts. IEEE-754 stays intentionally outside initial scope.

## Resource backend reconnaissance: 2026-11-14

The optional arlib model now proves that an extra result-preserving lookup
scan doubles its exact comparison cost and violates the old singleton budget.
Pinned realization/scan modules compile, as do selected Lax cost/NREST modules
under 4.35, the order-maintenance machine examples at their original pin, and
an isolated Std.WP worksheet over the existing independent Rust lookup result
specification. Main dependency pins and production source remain fixed.

This is partial reconnaissance, not a Rust runtime theorem. Structural key
comparisons, hit witness copies and source control flow still need an adequate
source-event interpretation. The pinned Lean backend rejects Aeneas fuel mode.
[Executed scope and obligations](../docs/planning/lean-complexity-campaign/evidence/executed-g0-w02.md)
keep G1/SRC-01 open; no full application/source cost claim follows.

## Actual production uniform-index source refinement: 2026-11-14

Both optimized graph algorithms now call the integer-only production helper
`verified_assignment_core::uniform_pairs::uniform_pair_indices`. Pinned
Charon/Aeneas extraction and `Rust/UniformPairs.lean` prove its termination,
checked increments/vector-length safety, exact original-coordinate output,
index/deletion bounds, duplicate-free rows and live pair count. The base and
every valid original right deletion refine independent maximum matchings over
nonnegative exact ordered-ring weights (`source_base_maximum` and
`source_deleted_maximum`). Empty/asymmetric dimensions are included.

`source_pair_cells` connects the actual vector length to its represented finite
pair-set cardinality and bounds it by the smaller side. Capacity, allocator
failure, complete family sharing, graph scheduling and runtime correspondence
remain open. Uniform float recognition and score accumulation are tested caller
boundaries; IEEE-754 correctness is intentionally excluded. General production
Hungarian/source and graph-DP refinements remain open. No whole-backend
verification claim follows from this helper theorem.

All **3,717 main Lean jobs**, **50 graph Rust**, **17 exact-core Rust** and
**228 required-native installed Python tests** pass. A three-sample installed
API check is recorded in [the milestone evidence](../dev/benchmarks/2026-11-14-uniform-source.md).

## Matching-family pair-storage bounds: 2026-11-14

`Complexity/MatchingFamilies.lean` counts separately tagged cells for each
materialized repair, sharing the base on unused deletions. Feasible base/repair
certificates derive at most `k+k²` retained pair cells per family, and at most
`2*left*right`. No runtime or optimum oracle is supplied. The concrete uniform
family closes all feasibility premises using its proved constructions.

Finite-sum factorization and Mathlib's handshaking/tree-edge theorems then give
`8*(n-1)*(m-1)` pair cells for degree-indexed collections, with a generic theorem
for arbitrary feasible weighted families and a premise-free uniform instance.
This establishes a model-level witness-storage component, not the complete DP
space or source-runtime theorem. Actual vector uniqueness/capacities, aliasing,
state scheduling, caches, arenas and other buffers still need resource
correspondence. IEEE-754 is outside the initial proof scope. All 3,716 main
Lean jobs pass; production Rust/Python code and benchmark target are unchanged.

## Complete uniform right-deletion family mathematics: 2026-11-14

`Shared/UniformMatchingDeletion.lean` now proves
`uniformRightDeletion_isMaximum` for every finite complete uniform instance,
nonnegative exact weight and deleted original right vertex. The concrete
construction follows the production cases: retain the base for unused columns,
replace a used column by the first unused original column when the right side
is larger, or discard its diagonal pair when the right side is smaller/equal.
Both projections remain injective, deleted vertices are absent, and optima are
over independently valid partial matchings. A generic surviving-cardinality
bound is derived, not supplied as an optimum premise.

The full main Lean build passes 3,715 jobs. Rust/Python sources are unchanged
from the tested/benchmarked implementation, so no extra performance campaign
or wheel rebuild was needed. These are mathematical construction and witness
proofs over exact ordered-ring weights; actual Rust/FFI refinement, nonuniform
matching correctness and total time/space correspondence remain separate.
IEEE-754 correctness remains deliberately outside the initial proof scope.

## Optional arlib operation-count experiment: 2026-11-14

The isolated project `experiments/arlib_cost` pins arlib to `8d08f89a` and
retains exactly the main Lean/Mathlib/Aeneas and transitive dependency revisions.
Its joint 3,744-job build, including the entire main library, succeeds. A sealed
queue lookup is proved equal to the existing `memoFind` value and comparison
counter for every table, with total recorded operations bounded by `2*n+1`
and constant recorded work on an early first hit. Three negative compilation
checks reject specification-view/cost-erasure access. Separate model-exchange
lemmas expose linear-list and assumed constant-time dictionary rates.

This is a real bridge to the existing lookup, not a `pure` wrapper around a
costly computation. It counts whole-key comparisons as abstract primitives;
structural equality internals, input encoding, space ownership and production
Rust resource correspondence are not proved. The program audit is bounded and
manual, not a general automatic sealing guarantee. Keep arlib optional: main
manifest/toolchain pins are unchanged, current memo counters remain the near-term
foundation, and expected hashing/full paper complexity are still open. See the
[executed experiment](experiments/arlib_cost/README.md) and its `results.json`.

## Uniform complete matching fast path: 2026-11-14

The production graph matcher now recognizes complete equal-positive-weight
matrices and constructs cardinality-optimal base/deletion witnesses directly.
Nonuniform, missing or nonpositive entries retain the existing general path.
All 50 graph Rust tests and 228 normal installed tests pass, including the
exhaustive injection/deletion suite and independent star vertex/edge bounds.
A source-only `d858a55` portable ABI3 rebuild also passes all 228 tests on
glibc 2.28 and every CPython 3.10–3.14, with strict auditing clean. It includes
the structural reference API and its explicitly open indexed proof boundary.

`Shared/UniformMatching.lean` proves uniform scores depend on cardinality,
full smaller-side matchings are optimal, and a concrete diagonal finite set
is feasible, has the required cardinality and is independently maximum. This
uses exact ordered-ring arithmetic, with no IEEE-754 identification or new
axioms. It is a mathematical fast-path justification, not a Rust control-flow,
index conversion, deletion-family or runtime-refinement proof. Those production
obligations remain open. The full Lean build passes 3,714 jobs.

## Structural isomorphism reference Python access: 2026-11-14

The existing actual structural Rust solvers are now accessible through both
Python ordered APIs as opt-in unweighted `reference-rust`. They still supply
the structurally optimal word and score covered by
`Rust.OrderedIsomorphism.rooted_common_isomorphism_of_trees` and
`largest_common_isomorphism_of_trees`. New Rust indexed reconstruction drops
whole child subtrees and searches one common original parent; token emission
returns original positions for Python/NetworkX readback. These new functions
are extracted and independently tested, **not source proved**. Do not transfer
the old structural theorem to this new indexed/token composition without its
missing refinement proof.

Pinned regeneration and its clean comparison succeed. All existing Lean
proofs compile in the full 3,713-job build, and both example suites pass. All
10 ordered-core tests and 219 installed tests pass, including five ABI3
runtimes. Exhaustive subset oracles check both root policies on 1,058 pairs;
160 unique-token cases check original-index feasibility and optima. The new
reference remains exponential (625× slower than optimized Rust on an eight-pair
star), with no production/default or runtime-verification claim. IEEE-754 is
outside the initial proof scope, independently of these discrete proof gaps.

## Infinite distance penalties exposed: 2026-11-14

Both graph backends now accept the paper's positive-infinity penalty, which
forbids skipped vertices. Native execution reuses optimized isomorphism with
the same root policy; the Python exhaustive oracle independently rejects
long-path candidates. Both structured and bare-pair rescorers enforce the
restriction. All 48 graph Rust and 209 installed Python tests pass, including
each host ABI3 runtime. This is API/test evidence. The existing `WithTop`
mathematical penalty model is preserved; no new production-source, witness
or complexity proof is claimed. IEEE-754 correctness remains outside the
initial proof scope stated above.

## Python integration and software-first sequencing: 2026-11-14

The existing graph Rust DPs for both Droschinsky families are now exposed
through public NetworkX APIs, with original-node/path witnesses, signed and
callback weights, empty/nonempty objectives and independent exhaustive Python
references/rescorers. The public exact assignment and partial-matching APIs
call the actual source-proved integer cores. Python conversions, callback
tables and PyO3 wrappers are tested boundaries, not Lean-proved boundaries.
The floating-point graph algorithms are not covered by those exact integer
source proofs, and their optimized schedules/runtime proofs remain open.

Ordered PyO3 integration now also validates typed tokens, propagates missing
original-node mapping errors, accepts unhashable mapped affinity values and
rejects invalid/overflowing f64 affinities. These legacy production extensions
are independently tested, not newly covered by the unweighted Boolean-core
Lean theorem. The existing verified token parser/solver and its proof boundary
are unchanged. The latest installed wheel passes 149 tests with all required
compiled backends executing.

The optional Rust-only ABI3 build compiles the same cores with PyO3's limited
API. Strict binary auditing and 149 tests on each CPython 3.10–3.14 validate
packaging/runtime behavior; they add no Lean claim about Python/FFI conversion
or the floating-point graph production implementations.

The public ordered isomorphism APIs also expose their existing root-preserving
level state as `rooted=True`. Independent parent-preserving subset enumeration
checks optimum, original indices and fractional witness scores across Python,
Cython and legacy PyO3 Rust. All 153 installed-wheel tests pass, including the
ABI3 runtime matrix. This weighted production implementation is still outside
the existing structural unweighted `Rust.OrderedIsomorphism` source proofs;
no new source-refinement or runtime theorem is claimed by the API exposure.

The balanced API's token boundary now supports hashable token objects without ordering
and all Python Unicode, including lone surrogates. Python/Cython tie selection
uses only the objective, and legacy Rust joins original Python token objects
after solving. Independent token-subset/roundtrip tests pass in the 161-test
normal and ABI3 suites (each CPython 3.10–3.14). These are tested runtime/FFI
changes; the existing Boolean-token source proof and its boundary are unchanged.

Substantial remaining formalization is deferred until public functionality,
independent correctness and measured efficiency are established. All existing
proofs are preserved; full mathematical, production-source and applicable
complexity verification still blocks the final verified release. Development
wheels and implemented algorithm use do not depend on finishing these proofs.

The production f64 2016 solver now reuses related child matchings through a
right-deletion family kernel. Independent injection enumeration checks deletion
objectives and original indices; 44 graph Rust and 163 installed Python tests
pass, including five ABI3 runtimes. Dense family arithmetic is O(k²l), but no
new Lean recurrence, refinement or runtime theorem is claimed. Its f64 dual
repair is distinct from the source-proved exact sparse augmentation and
partially verified exact deletion caller below. At that milestone, full graph witness
materialization and 2018 optimized scheduling remained open.

Graph production states now retain constant-size score/choice IDs, with only
the winning mapping expanded at the boundary. Independent original-index/path
checks continue to pass (44 native, 163 installed Python tests). Full witness
copying is removed and measured memory/runtime improve, but the choice pool,
tie rule and f64 graph implementation have no new source-refinement or runtime
theorem. Existing mathematical/exact-core proof endpoints are preserved.

2016 production memoization now uses a dense table of fixed-left/oriented-right
states, with binary-search parent and edge lookup. Matching-family reuse and
choice storage supply a written operation-count argument for the published
2016 target under explicit arithmetic/query costs. All 44 native and 165
installed Python tests pass. This argument and measured scaling to 512-node
inputs are not a Lean complexity theorem or actual-source refinement; those
remain open alongside f64 arithmetic correspondence and the 2018 schedule.

The production 2018 schedule is now implemented: fixed-left postorder mapped
matching families, two-pass right skip messages, and the two structural
highest-vertex cases including a cardinality-two join from distinct branches.
Independent exhaustive path/callback tests pass (44 native, 172 installed
Python tests, all five ABI3 runtimes). This is implementation/test evidence,
not a new Lean structural dichotomy, evaluation-order, witness or actual-source
proof. Logarithmic view/edge lookup also remains an implementation gap to the
precise 2018 bound. Existing recurrence and reference evaluator proofs remain
preserved; full verification is still required for the final verified release.

Directed-edge view IDs and original edge indices now remove parent/label
searches from both production solvers; scalar and callback-table branch queries
are constant time. A written operation-count argument now matches the 2018
core bound with explicit arithmetic/scoring assumptions. All 44 native and 172
installed tests pass, including five ABI3 runtimes. This closes an implementation
cost gap, not any Lean dichotomy, choice-witness, source-refinement, f64 or
complexity obligation. Those proofs remain required for the final release.

Public result-object rescoring now independently checks the supplied simple
path families, injectivity, disjoint interiors, original edges and connected
common skeleton, then applies the paper's scoring rule. Small signed cases
also compare the separate exhaustive bare-pair validator. All 176 installed
tests pass (normal required-native and five ABI3 runtimes), including malformed
path witnesses. This enables independently rescored 512-node benchmarks but
adds no Lean validation, source-refinement or asymptotic proof. The native
solver binaries and all mathematical/source proof endpoints are unchanged.

2018 now omits global-left-root deletion matchings and skipped messages that
neither structural optimum case queries. Independent forbidden-root path and
parent-deletion regressions still pass (44 native, 176 installed tests, all
five ABI3 runtimes). Star512 improves 5.10× in repeated installed measurements.
This is tested production optimization; the dependency argument, skipped-
highest decomposition and actual source refinement still need Lean proofs.

The Rust-only CP310 ABI3 wheel now builds from source in a pinned manylinux_2_28
x86_64 environment. Linux/ABI audits are clean; 176 tests pass on glibc 2.28 and
each CPython 3.10–3.14, and two timestamp-controlled builds are byte-identical.
This extends packaging evidence only. Mathematical, production-source, f64 and
formal complexity obligations remain unchanged; the package is not a fully
verified release. Remote CI and other stable-ABI platforms remain pending.

Both graph Python/PyO3 families now expose fixed ambient roots and the separate
root-to-root restriction through the production Rust `RootConstraint` policy.
Existing independent Lean rooted predicates/recurrences supply their mathematical
contracts. Independent subset/bijection/path oracles, NetworkX ancestor-path
checks and original-node rescorers pass, including signed forced roots and
actual high-degree deletion repair in each policy (47 native, 199 installed
tests; all five host ABI3 runtimes). These are tested production/API additions,
not new source-refinement or complexity theorems. The preceding manylinux
artifact's 176-test evidence remains separate until its source is rebuilt.

## Accepted development: 2026-11-14

`cd proofs && lake build` succeeds under Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and Aeneas
`5a392f4b80a4d0d05abc240eb2a7fa70622a9a35`. This is an executed VM build,
not a maintainer-reported build. All maintained modules are imported by
`SubtreeProofs.lean`. Reproduction commands, pins, translation boundaries,
and bind-mount instructions are in [VERIFICATION.md](VERIFICATION.md).

The prior opt-in `BaselineAudit.lean` endpoint review established the initial
allowed set `propext`, `Classical.choice`, `Quot.sound`; raw output was captured.
The opt-in module also names newer endpoints for a later final dependency
review. Routine development checks are targeted compilation, not repeated audits.

All ordered-tree declarations below have prefix
`SubtreeProofs.Paper2004.OrderedTree`.

| Module / declaration | Accepted claim and hypotheses |
| --- | --- |
| `OrderedTree`: `ContractStep.edgeCount_decreases`, `embeds_edgeCount_le` | Independent root-preserving ordered contraction strictly decreases edges; its closure cannot increase edges |
| `BalancedSequence`: `encodeDyck_semilength` | Encoding semilength equals the tree's edge count |
| `EncodingEquivalence`: `decodeDyck_encodeDyck`, `encodeDyck_decodeDyck` | Both encoding round trips, on every tree and every Dyck word |
| `ContractionSoundness`: `contractStep_encodeDyck`, `embeds_encodeDyck` | Independent tree contractions induce pair deletions |
| `ContractionCompleteness`: `dyckContractStep_decodeDyck`, `embeds_iff_dyckEmbeds` | Pair-deletion completeness and the two-way semantic bridge |
| `PaperContainment`: `PrintedContains.toDyckEmbeds`, `PrintedContains.toTreeEmbedding` | Literal printed Definition 2 implies operational containment |
| `PrintedContainmentCounterexample`: `branching_example_not_printed`, `printed_containment_not_complete` | The literal least recursive relation excludes the valid `001011 → 0011` contraction |
| `PrintedContainmentCounterexample`: `branching_example_printed_common_at_most_one`, `branching_example_operational_common_optimal` | Printed and operational optima differ on that pair |
| `ContractionOracle`: `mem_contractOnce_iff` | Executable one-step tree enumeration is exactly `ContractStep` |
| `ContractionOracle`: `contractions_complete`, `mem_contractions_iff` | Edge-count fuel suffices for every embedding; full enumeration equals `Embeds` |
| `ContractionOracle`: `singleton_embeds`, `mem_commonContractions_iff` | Feasible candidates exist and the common-candidate list equals `CommonEmbedding` |
| `ContractionOracle`: `maximumCommonContraction_correct` | Executable exhaustive oracle returns an explicit `IsMaximumCommon` tree for every pair; no efficiency claim |
| `Shared/WeightedMatching`: `SubtreeProofs.WeightedMatching.solveMatrix_correct` | Executable finite partial-matching oracle is globally optimal for every rectangular integer-weight matrix, including forbidden pairs and empty sides |
| `Rust/ContractionBudget`: `SubtreeProofs.Rust.contractionBudget_refines_tree` | Real translated Rust succeeds and returns the contracted tree's edge count, assuming the input `u32` represents the original count |

The matching specification permits unmatched vertices and an empty matching.
The contraction oracle's specification permits the singleton (zero-edge)
tree, rather than an empty forest. The Rust spike does not verify a solver.

## Compact original-index deletion warm starts and source caller: 2026-11-14

`Shared/AssignmentFiniteDeletion` uses Mathlib's increasing `Fin.succAbove`
embedding to enumerate exactly the surviving original vertices, proves its
exact skip-index expansion/compression formulas, and transports the bypassed
permutation into compact coordinates. Every nonfree row keeps its old edge;
the unique temporary completion joins the actual surviving old free row and
column. Paired deletion retains every surviving edge.

`AssignmentReindex` preserves exact assignment/dual objectives, sparse
feasibility, compatibility, minima and two-sided envelopes under coordinate
equivalence. `AssignmentCompactDeletionState.compact_deletion_state` proves
the projected warm start preserves sparse feasibility, the full two-sided
envelope and exact dual accounting with the removed contributions subtracted,
and derives the surviving dimension's cumulative bound from identity edges.
The removed baseline coordinates are zero, as for paper right-vertex/copy
deletion. `compact_seed` proves all nonfree projected edges remain allowed and
tight. `Rust/SparseDeletionIndices` verifies actual source compression on all
represented scalars and its exact correspondence with this equivalence.

The actual Rust `sparse_deletion::repair_deleted_sparse_vertex` now projects
the graph/potentials, bypass-completes the surviving assignment, reuses fixed
deletions or calls one verified sparse augmentation, and exports original row
and column indices. It translates, and all fifteen exact-core tests pass,
including 546 deletions of certified old optima through dimension six against
exhaustive induced-graph optima, both reuse/repair branches, feasible/tight
returned duals and malformed inputs. Its complete projection/caller source
refinement, original partial-matching family integration and optimized runtime
remain open; tests do not replace those Lean obligations.

## Actual single-path sparse augmentation verified end to end: 2026-11-14

`Rust/SparseAugmentationEntrypoint.augment_sparse_permutation_spec` proves
the actual public Rust search-plus-flip wrapper returns an independently
minimum compatible permutation from a represented completed permutation
whose nonroot edges are allowed and tight under a feasible dual. Inputs obey
the paper's two-sided nonpositive initial-potential envelope and exact dual
accounting, with nonpositive allowed i64 costs and u32-bounded dimension. A
compatible perfect assignment supplies feasibility of repair; no optimum,
path, inverse/rank table, loop output or machine-success certificate is a
premise. The exact returned row-index vector represents the canonical path
augmentation, its exported physical potentials remain feasible and are tight
on the returned assignment, and rows outside the path retain their old edges.

`SparsePathFlipEntrypoint.flip_sparse_path_spec` proves the actual checked
flip routine itself: positive decreasing ranks construct a finite simple trace
internally; source counter/array/rank checks succeed; every returned original
row coordinate equals the inverse column-cycle augmentation. Its invariant,
local-bound derivation, exact prefix writes and complete loop termination are
proved in `SparsePathFlipInvariant`, `Bounds`, `Preservation` and `Loop`.

This closes the actual generic one-deficit augmentation source refinement.
The copied-graph initialization/deletion caller, exact original matching
family integration and the paper's optimized sparse priority-queue/runtime
remain open. The current selector scans the whole optional matrix at each
step, so the verified reference makes no published optimized cost claim.

## Actual path certificate, prefix semantics and flip loop body: 2026-11-14

`Rust/SparsePathCertificate` interprets the actual returned predecessor indices
as finite original graph vertices. Every positive-rank coordinate is proved in
bounds, so the unused-coordinate default introduces no path edge. Its
`PathCertificate.exists_optimal_augmentation` derives the independent optimal
ranked augmentation directly from the actual search certificate and compatible
old nonroot matching edges.

`Shared/AssignmentTracePrefix` proves that one predecessor-row overwrite
extends the exact final-value prefix and that exhausting the trace yields the
canonical augmentation permutation, including unchanged rows outside it.
`Rust/SparsePathFlipBody.flip_body_step_spec` proves the actual active flip
iteration performs precisely that row write and either stops at the root or
follows the old assignment to a smaller positive discovery rank. Checked
counter increments and all predecessor/parent/rank reads and writes succeed
under the local bounds that the complete loop must derive.

The actual full flip-loop invariant/termination, public augmentation wrapper
and deletion driver are still open. These supporting results do not substitute
for the remaining public source-refinement endpoint.

## Ranked augmentation mathematics and actual path-flip reference: 2026-11-14

`Shared/AssignmentRankedTrace.exists_ranked_predecessor_trace` constructs a
finite simple original-column trace from positive strictly decreasing ranks.
`PredecessorTrace.formPerm` proves that Mathlib's canonical list-cycle
permutation follows the original matched column of each predecessor row,
closing at the free target. `AssignmentRankedAugmentation` uses the inverse
column cycle to assign every predecessor row to its discovered column and
retains all other old nonroot edges.

`exists_ranked_augmentation` derives an independently minimum compatible
assignment from a feasible dual, allowed/tight old nonroot matching edges,
tight real predecessor edges and decreasing positive ranks. No repaired
optimum or separately supplied path is assumed. It also proves unchanged
assignments outside the trace. This is independent augmentation mathematics;
the maintained Rust flip loop's refinement is still open.

The actual Rust `flip_sparse_path` and `augment_sparse_permutation` reference
now exist and translate. The flip checks shape, root/target, predecessor/parent
bounds, positive decreasing ranks and the visit bound. The thirteen-test
exact-core suite passes, comparing both public routines against the independent
path flip and exhaustive permutation optima on the 120 constructed sparse
states, with additional malformed-path/rank checks. `Rust/SparsePathCopy`
proves its actual copy loop preserves every original assignment index in
order for every represented slice. The actual flip's permutation/optimality
refinement, deletion driver and optimized runtime remain open.

## Actual sparse augmenting-path search verified end to end: 2026-11-14

`Rust/SparseSearchEntrypoint.find_sparse_augmenting_path_spec` proves the
actual public Rust search succeeds from a represented completed permutation,
a selected root, feasible sparse potentials, tight completed-permutation edges
except at that root, the two-sided nonpositive initial-potential invariant,
exact dual accounting, and existence of a compatible perfect assignment.
The source matrix has nonpositive allowed i64 costs and u32-bounded dimension.
No inverse table, cut minimum, path, rank, loop result or arithmetic-success
certificate is assumed.

`SparseSearchInitialization` derives the complete initial invariant from the
actual zero-filled vectors and root flag write. `SparseSearchLoop` proves
termination and the stopped invariant by the decreasing visit measure. The
returned `PathCertificate` preserves sparse feasibility, all old nonroot edge
tightness, two-sided numeric bounds/accounting, original-coordinate allowed
tight predecessor edges, the actual free target, strictly decreasing positive
predecessor ranks and at most `n` recorded steps.

The entry point returns a ranked predecessor path and updated potentials;
it does not yet flip that path or return a repaired permutation. Compatibility
of unchanged old matching edges is needed by that subsequent augmentation
proof. Executable path flipping, the copied-graph deletion driver and the
paper's optimized priority-queue/runtime obligations remain open. The current
full-matrix cut scan remains a reference implementation.

## Complete sparse search-body invariant preservation: 2026-11-14

`Rust/SparseSearchPreservation.body_preserves_spec` proves that an actual
active Rust iteration preserves the entire independent search invariant and
strictly decreases `n + 1 - steps`. The exact output frame is supplied by the
previous loop-body refinement; no post-state invariant is a premise.

`SparseSearchTightness` retains old real matching and discovered predecessor
edges under the physical potential update. `SparseSearchGrowth` covers both
terminal and nonterminal flag branches, free-target preservation and exact
visit accounting. `SparseSearchRanks` proves the actual vector writes record
the next positive discovery count, preserve earlier edges and ranks, and make
every new predecessor either the root or point to a strictly earlier discovered
matched column. `afterStep_invariant` combines those results with the proved
feasibility, two-sided envelope and objective accounting of the returned
potential vectors.

The complete finite-loop theorem, source entry-point initialization/output
refinement, path flip and deletion driver remain open.

## Actual sparse alternating-search loop body: 2026-11-14

`Rust/SparseSearchBody.body_step_spec` proves one complete actual active Rust
iteration from the combined independent invariant. The visit guard, counter
increment, attained cut/update, predecessor/rank writes, inverse-table read
and both selected-flag writes all succeed. Its exact `afterStep` frame records
the real terminal/nonterminal branch and all returned vectors, original-index
predecessors and discovery ranks. Every source error branch in that iteration
is ruled out from the input/state hypotheses.

This is a source loop-body refinement. Preservation of the entire combined
invariant by its exact returned state, the finite complete-loop theorem,
entry-point initialization and executable path flipping remain open.

## Actual search flags and combined invariant: 2026-11-14

`Rust/SparseSearchFlags` proves that zero-based Boolean-vector writes
represent the independent selected sets exactly. The root initialization is
a singleton; a nonterminal column/inverse-row pair of writes implements the
inverse-image alternating-cut extension, adds exactly one selected column,
and strictly decreases the remaining-column measure.

`Rust/SparseSearchInvariant` combines physical vector lengths, exact selected
sets, the free target, visit accounting, sparse dual feasibility, two-sided
envelopes and objective accounting, old matching tightness, and original-index
predecessor/discovery-rank conditions. The compiled `Invariant.visit_guard`
derives the actual source's visit limit; `Invariant.advance_spec` discharges
all inputs of the actual selector/update composition from that state. The
complete loop's preservation of this invariant, initialization-to-output
refinement and the executable path flip remain open.

## Sparse alternating-search reference and verified inverse initializer: 2026-11-14

The maintained Rust `sparse_search::find_sparse_augmenting_path` now performs
an alternating search with the proved allowed-edge cut/update primitive. It
takes a completed permutation whose root edge is temporary, preserves the
remaining assignment during search, and records original-coordinate
predecessor rows and positive column discovery ranks. It checks dimensions,
permutation validity and root bounds, and reports exhausted/absent cuts and
arithmetic errors explicitly. Its full-matrix cut scans make this a reference
search, without the paper's sparse priority-queue runtime claim.

`Rust/SparseSearchInverse.inverse_completed_spec` proves the actual seed
validator/inverse-table loops succeed for every represented permutation and
return its exact inverse, including all checked array writes and termination.
The complete alternating loop's feasibility/tightness, predecessor-rank,
termination and output-path refinement remain open; native results do not
substitute for that Lean endpoint.

The twelve-test exact-core suite passes. New independent tests exercise 120
single-deficit sparse states through dimension five, including nonidentity
completed permutations and nonzero feasible potentials on both sides. They
follow the returned predecessor rows, check strictly decreasing positive
discovery ranks, flip the resulting path, and compare the complete tight
assignment and dual objective against exhaustive permutation optima. Malformed
shapes/permutations, an invalid root and an absent cut are also covered.

## Alternating sparse-cut growth and old-edge tightness: 2026-11-14

`Shared/AssignmentSparseSearch` describes a deficient matching by completing
its free row/root to its free target column. Until the target is reached,
selected rows are exactly the root plus inverse images of selected columns.
The module proves this is a one-excess-row cut, that every nonterminal new
column adds a fresh matched row and preserves the deficit, and that the
finite complement of selected columns strictly decreases. The component cut
update preserves every old real matching edge's tightness because both
endpoints lie in the cut together; the temporary completion edge is excluded.

`exists_search_adjustment` derives an attained allowed sparse adjustment
from feasibility and a compatible perfect assignment. It preserves sparse
feasibility and all actual old tight matching edges, creates a new tight cut
edge, and either reaches the free target or supplies a fresh matched row.
These are independent search lemmas, not yet a refinement or runtime theorem
for the complete Rust alternating-search loop.

## Actual composed sparse search step: 2026-11-14

The Rust `sparse::advance_sparse_cut` now selects an actual minimum allowed
crossing edge and applies its zero-based potential adjustment. The maintained
`Rust/SparseCutStep.advance_sparse_cut_spec` proves success from the independent
two-sided paper state, sparse feasibility, exact dual accounting, a compatible
perfect-assignment witness and a one-excess-row search cut. No cut minimum,
path, arithmetic-success certificate or externally supplied potential bound
is assumed. `SparseCutBiInput` derives the scanner's `2^96` potential frame
from the dimension/weight budget, including nonzero initial columns.

The returned `StepProgress` records the exact original minimum edge, both
physical vector lengths and component updates, sparse feasibility, the
two-sided envelope, exact dual progress, the next cumulative bound, and an
actual original edge made tight across the search cut. Native cut/update
composition tests exercise the public wrapper as well as its constituent
primitives. This closes one actual dual-search step. Growing the alternating
search, constructing/flipping its path, the deletion repair driver and the
published optimized running time remain open.

## Actual zero-based sparse potential updates: 2026-11-14

The maintained Rust `sparse::adjust_sparse_cut` now applies a nonnegative cut
increment directly to zero-based potential slices, matching the coordinate
convention of `minimum_sparse_cut`. Selected rows increase and selected
columns decrease; inputs are borrowed and unchanged. Shape, size, negative
increment and checked overflow produce explicit errors. Two single-vector
passes keep this implementation within the pinned Aeneas translation subset.

`Rust/SparseCutUpdate` proves exact full-vector coordinate readback for the
actual loops. `SparseCutUpdateSafety.adjust_sparse_cut_bi_safe_spec` derives
all checked ranges from sparse feasibility, an actual compatible perfect
assignment, a one-excess-row minimum-cut condition, and the two-sided
nonpositive initial-potential envelope. The returned physical vectors equal
the independent ideal adjustment at every original coordinate, preserve sparse
feasibility and the envelope, and satisfy exact dual accounting and the next
cumulative bound. No arithmetic-success premise is supplied to that endpoint.

The exact-core native suite adds cut/update composition tests over sparse
matrices, every one-excess-row mask through dimension four, nonzero potentials
on both sides, feasibility, newly tight selected edges and exact objective
progress. Error cases cover dimensions, negative increments and both overflow
directions. This is a verified update primitive; the sparse augmenting-search
caller, repair driver and optimized runtime are still open.

## Original-index decoding after single-cycle deletion repair: 2026-11-14

`Shared/CopiedMatchingDeletionDecode.surviving_minimum_decodes` proves that
an independent minimum compatible assignment on the actual induced surviving
copied graph decodes to maximum partial matchings for `deleteRight weights
removed`, with surviving vertices retaining their original indices. The
proof extends the surviving permutation by the removed zero identity edge,
preserves the exact objective, and compares against every compatible
assignment for the deleted matrix. Every such assignment fixes the removed
vertex because all incident cross edges are absent.

`matched_single_cycle_decodes` combines this with the existing cycle repair:
from a feasible/tight compatible old assignment and an actually matched right
vertex, there exists one cycle repair whose original and copy decodings are
independently maximum for the deleted instance, and all old assignment edges
outside that cycle stay unchanged. This closes the mathematical decoding
obligation; constructing that cycle efficiently in the actual Rust source
and proving the paper's runtime remain open.

## Two-sided copied-graph potential safety: 2026-11-14

`Shared/AssignmentBiEnvelope` tracks independent initial row and column
potentials, proves preservation by cut updates, and derives the cumulative
bound `n * (costUpper + 2 * initialBound)` by sparse weak duality. Its deletion
lemma restricts both potential families and subtracts the exact removed
contributions from the cumulative increment. Both removed baseline values
must be zero; feasibility on a zero-cost identity edge makes the new
increment nonnegative.

`Shared/CopiedMatchingEnvelope.initial_bi_state` instantiates the envelope
and feasibility with the paper's actual row-maximum initial potentials on
both sides. `deleted_bi_state` proves that deleting a right vertex and its
copy preserves sparse feasibility, the two-sided envelope and exact dual
accounting, with increment at most `2 * survivingDimension * weightBound`.
The compatible perfect assignment needed for this budget is constructed
from surviving identity-copy edges; no repaired optimum is assumed.

`Rust/SparseBiAdjustment.adjust_potentials_bi_safe_spec` verifies the actual
shared Rust potential-update routine under these two-sided invariants for
nonpositive allowed costs and initial potentials in `[-2^63, 0]`. It derives
every checked arithmetic range, preserves sparse feasibility and the
two-sided envelope, and proves exact objective/reserved-slot accounting.
This extends the earlier zero-initial-column update theorem to the genuine
paper initialization. The sparse augmenting-search caller and efficient
deletion-repair implementation remain open.

## 2004 algorithm and state bounds: 2026-11-14

New compiled endpoints (same ordered-tree prefix):

- `OptimalEncoding.longestCommonBalanced_decodes_maximum` (declaration
  `longestCommonBalanced_decodes_maximum`) proves Theorem 2 using operational
  containment and the independent tree optimum.
- `BalancedDecomposition` (namespace `SubtreeProofs.Paper2004.BalancedDecomposition`)
  proves Lemmas 1--6 and Fact 2, including `states_front_append`,
  `states_eq_front_union_head` and `headContractions_card_depth`.
- `card_true_leaf_bounds` supplies a corrected proof using the actual-leaf
  recurrence: D has at most `(n+1)*leaves` states and S has at most
  `n*leaves+1`. Its empty-tail branch avoids the printed recurrence error.
- `TreeStateBounds.trueLeafMeasure_encodeDyck` and
  `sequenceDepth_encodeDyck` identify the sequence measures with the
  independently defined tree measures. `decomposition_card_bound` proves
  Theorem 1 in actual tree depth and leaves, without a state-size assumption.
- `DynamicProgram.dyckEmbeds_first_pair` proves the structural completeness
  split of operational contraction. `paperCommon_sound`, `paperCommon_upper`
  and `paperCommon_correct` prove Lemma 8 with an explicit balanced-word
  witness; `paperCommon_tree_correct` proves the returned decoded tree is
  `IsMaximumCommon` for every pair of input trees. The separate numeric
  computation is certified by `paperLcs_optimum`.
- `LinearEncoding.encodeAccum_linear` proves Fact 1 for an accumulator encoder
  using only output list constructors. `encodeAccum_cost` counts exactly
  `5*edgeCount+2` constructor visits and output allocations.

The witness recursion computes an optimum tree. The separate memoized numerical
algorithm below shares states and has actual operation counts; full runtime
refinement remains open.
The distinct ordered-isomorphism contract, full implementation cost model,
index mapping witnesses and Python integration remain open.

## Memoization accepted: 2026-11-14

`MemoizedDynamicProgram.memoLcs_optimum` proves the actual threaded memoized
score computation attains the independent optimum. `memoLcs_nodup` proves
no key is inserted twice; `memoLcs_new_keys` confines additions to the D-product.
`memoLcs_counts` ties misses to actual table growth and bounds actual calls by
four times misses plus one. `memoLcs_operation_bound` and
`memoLcs_tree_operation_bound` combine these with the proved finite state bounds.
`memoLcs_comparison_state_bound` accounts for the association list's linear
lookup scans: at most `(4*S+1)*S` key comparisons for S product states.

The table-operation bound has the paper's state-count scale, while this
association-list implementation has the explicitly proved extra comparison
factor. Structural word comparison, first-return splitting and word
canonicalization costs still need an implementation-level model. Expected-time
hashing and the full Theorem 3 runtime are not claimed by these operation counts.

The shared matching proof now works over any linearly ordered additive
commutative monoid, including integers and reals. Integer instantiations remain
executable. No compatibility with the CLRS-Lean Hungarian implementation is
assumed; its inspected source pin uses Lean/Mathlib 4.32.0-rc1.

## Actual Rust solver accepted: 2026-11-14

`Rust.OrderedSolver.largest_common_embedding_of_trees` proves successful
execution of the real translated `verified_ordered_core::largest_common_embedding`
for every independent ordered-tree pair below 2^32 edges per input. Its result
is an `IsMaximumCommon` tree with an exact reported edge count. The supporting
proofs cover representation round trips, real Rust copying and concatenation,
score-based tie selection, termination and checked-addition safety.

This is an initial exponential reference solver with a structural tree witness.
It is not the memoized/optimized Rust implementation, an input-index embedding
map, or an integrated Python backend. The generated definitions come from the
maintained safe Rust source and the pinned extraction script. Its compiled endpoint adds
no dependencies outside the reviewed baseline. An independent Rust oracle
checks all 38,809 ordered pairs of the 197 trees through six edges, including
returned-witness feasibility and exact scores. The OS-level
allocator/stack budget is outside the Aeneas functional semantics.

## Actual Rust memoization accepted: 2026-11-14

`Rust.MemoizedOrderedSolver.maximum_common_embedding_of_trees` proves the
memoized entry point returns an independent maximum common tree and exact
score under the same u32 input bounds. The supporting invariant certifies
cached witnesses, source equality/copying/lookup/insertion, and termination.
Its returned cache refines the separately verified numeric memo table exactly;
`memoized_common_embedding_cache_bound` proves actual cache-key uniqueness
and the D-product size bound. No caller-supplied cache assumption is needed
for the public empty-cache entry point.

Both Rust solvers pass the full 38,809-pair six-edge contraction oracle.
Deterministic shape benchmarks and the remaining comparison/copy costs are
recorded in `dev/benchmarks/2026-11-14-ordered-memo.md`. The source algorithm
is now memoized but its linked-list table still pays a linear scan factor.
End-to-end Rust bit/word cost and expected-hashing complexity remain open.

## Dummy-assignment reduction accepted: 2026-11-14

`WeightedMatching.AssignmentReduction.minimum_assignment_decodes` proves the
full mathematical reduction from complete minimum-cost assignment on |L|+|R|
rows/columns to optional partial matching with forbidden pairs and arbitrary
signed real weights. `extend` swaps matched endpoints and fixes unmatched ones;
`decode_weight` proves exact objective preservation on decoding. Forbidden and
nonpositive entries have zero profit and are dropped during reconstruction.
No numerical sentinel or magnitude assumption occurs in the real theorem.

The Rust matching reference now follows that construction, retains selected
positive weights below the old 1e-9 cutoff, rejects nonfinite inputs and totals,
and validates ragged matrices before returning for an empty first row. The
35-test graph suite passes, including small exhaustive matching comparisons,
tiny-positive and large-magnitude cases, and invalid numeric inputs.
The floating Hungarian loop itself is not verified; real arithmetic equivalence
does not establish exactness under floating-point rounding or overflow.

## Unordered graph foundations accepted: 2026-11-14

`Shared.FiniteTree` uses Mathlib trees and proves canonical unique-path
orientation/length/interior properties. `Droschinsky2016.exists_maximum`
proves unconditional attainment for nonempty connected isomorphism witnesses,
scoring vertices and unordered edges once over `WithBot ℝ`. `Valid.inducedIso`
constructs the actual induced-graph isomorphism; both selected objects are trees.

`Droschinsky2018.exists_maximum` proves finite attainment for independent
unrooted skeletons whose paths have disjoint interiors. `pathScore_direct`
and `one_two_path_score` capture Definition 4's two scoring branches;
`maximum_score_antitone` proves the general finite-penalty monotonicity result.
The source problem preserves negative and negative-infinity optima. The default
reference APIs permit empty results; explicit nonempty Rust/Python entry points
retain negative scores and distinguish infeasibility with `None`.

Fixed ambient-root admissibility, graph DP evaluation/optimization and Rust
refinements remain open. The new
specifications and finite-existence results are not proofs of those algorithms.

## Fixed-root reduction accepted: 2026-11-14

`Shared.RootedTree` defines ancestry by the unique path and proves transitivity,
strict depth increase, injective-tree-map invariance, connected-subtree path
closure and `connected_exists_unique_top`. `Droschinsky2016.RootedValid`
specifies root-to-root witnesses inside independently defined descendant
subtrees. `Valid.fixed_root_representative` proves every unrestricted witness
belongs to the fixed-root family, with a unique representative mapped root.
`fixedRootValue_eq_unrootedValue` proves the exact variational equality of
2016 Lemma 2 for the independent score, including negative-infinity weights.
No dynamic recurrence appears in the definitions of these optima.

Child-matching decomposition/assembly and the actual rooted/unrooted graph
algorithms and cost bounds remain open. These structural results do not
verify the Rust graph solvers.

## Weighted branch decomposition accepted: 2026-11-14

`Droschinsky2016.Valid.ancestor_preserved` proves rooted ancestry preservation
from the actual induced-graph isomorphism and canonical paths.
`branchMapping_valid` proves that each mapped descendant restriction is a
nonempty connected isomorphism. `unique_child_branch`, `branch_partition`
and `child_branch_disjoint` give the exact disjoint vertex partition.
`edge_partition` partitions actual unordered common edges into root edges and
branch edges; `score_decomposition` proves the complete independent vertex/edge
score equals the mapped-root reward plus edge-and-continuation branch rewards.
It holds for signed and negative-infinity scores.

This proves the decomposition direction behind 2016 Eq. (1). Converse assembly,
optimal child selection, recursive evaluation and the cost theorem remain open.

## Rooted matching equality accepted: 2026-11-14

`BranchFamily.assemble_valid` proves the converse structural direction: any
injective child matching of independently valid descendant continuations
assembles into a nonempty connected induced isomorphism. Its branch restrictions
recover the exact supplied continuations, and `score_assemble` proves their
complete score. `rootedValue_attained` gives actual optimal rooted witnesses.

`Droschinsky2016.rooted_matching_recurrence` proves 2016 Eq. (1) against the
independent optimum for arbitrary finite rooted input trees and `WithBot ℝ`
scores. Forbidden non-neighbor pairs, unmatched children, signed weights and
negative-infinity optima are included. The supporting matching optimizer is the
certified finite exhaustive oracle; the continuation values are independently
specified optima, not an implemented recursive DP. Efficient evaluation,
state representation, Rust refinement and Proposition 1's runtime remain open.

## Topological source-witness direction accepted: 2026-11-14

`Shared.TopologicalEmbedding` specifies an independent common tree with an
injective map, canonical edge paths, no mapped vertices in edge interiors,
and disjoint interiors for distinct edges. `liftWalk_isPath` proves that
lifting an abstract simple path yields a target simple path; `ancestor_iff`
proves ancestry preservation/reflection. `toRooted` and
`branch_paths_intersection` establish both clauses of 2018 Definition 1
for corresponding chosen roots, with the root-to-root property explicit.

`Droschinsky2018.Valid.skeletonIso` constructs an actual isomorphism between
the selected skeleton trees. `Valid.rooted_realizations` constructs the common
tree and both source-style rooted embeddings, with their images recovering
exactly the original finite pair relation. Fixed ambient-root admissibility and the mapped/skipped recurrence remain
open; the subsequent reconstruction and local-source tranches prove the
converse source direction and exact score correspondence. The chosen-root result does not justify
the 2016 fixed-root shortcut for topological embeddings.

## Explicit-realization reconstruction accepted: 2026-11-14

`TopologicalEmbedding.selectedIso` proves that the selected-image skeleton of
an explicit independent path realization is exactly its abstract common tree.
Its tree and interior-disjointness invariants follow from the realization;
they are not additional hypotheses. `Droschinsky2018.pairedImage_valid` proves
two realizations yield a valid finite pair witness, and
`Valid.realizations_roundtrip` proves extraction/reconstruction preserves all
pairs. `score_pairedImage` equates the finite-pair score with the independent
sum over the abstract common tree's vertices and unordered edges, for every
finite or infinite penalty and signed/bottom scores.

The finite skeleton and explicit unrooted path-realization formats now agree
in both directions with exact scores. The local-source tranche below proves the converse from the source's two
rooted clauses to the global path invariant. Fixed ambient-root admissibility
and the two-state algorithm remain open.

## Finite floating-score behavior corrected: 2026-11-14

The Rust graph DPs and Python exhaustive references now retain positive scores
below 1e-9 and use exact score equality for tie breaking. Slightly better
candidates are no longer replaced or rejected as approximate ties. Both paths
reject queried nonfinite node/edge weights and accumulation overflow; Rust
panics and Python raises `ValueError`. Regression tests cover singleton and
child gains of 5e-12, alternatives differing by 5e-10, NaN/infinite values and
overflow. The full graph crate passes 39 tests; Python passes 65 with 3 skipped.
IEEE rounding and the actual Hungarian numerical refinement remain
open; these tests do not establish exact arbitrary-real implementation behavior.

## Full local-source correspondence accepted: 2026-11-14

`Shared.RootedFork` derives greatest common ancestors and distinct child
branches for incomparable vertices using finite canonical paths.
`RootedTopologicalEmbedding.ancestor_iff` proves both ancestry directions from
Definition 1's local conditions. `toUnrooted` derives global mapped-vertex
avoidance and distinct-edge interior disjointness; these are not assumed in
the source-style structure. No root-to-root assumption is needed for this
converse.

`Droschinsky2018.valid_iff_source_embeddings` gives an explicit equivalence
between the independent unrooted finite-pair witness and source-style rooted
embeddings for existential corresponding roots. `rooted_source_witness` and
`score_pairedImage` preserve the independent abstract-tree score. Fixed
ambient-root admissibility and the mapped/skipped recurrence remain open.

## Fixed ambient-root source contract accepted: 2026-11-14

`Droschinsky2018.RootedValid` requires an independently valid skeleton plus a
single mapped top pair above every selected vertex in both supplied input
orientations. `rootedValid_iff_source_embeddings` proves exact equivalence to
Definition 1 embeddings with those fixed ambient roots.
`RootToRootValid` is separate; `rootToRootValid_iff_source_embeddings` proves
its precise source correspondence with both root-mapping conditions explicit.
`rootedValue_attained` proves finite attainment for the independent rooted
objective, retaining signed/negative-infinity scores and infinite penalties.

Mapped/skipped boundary-state objectives, recurrence correctness, optimized
matching/evaluation, complexity and actual graph Rust refinement remain open.
The fixed-root admissibility result does not make the 2016 fixed-root shortcut
valid for 2018's unrestricted unrooted objective.

## Skipped-state recurrence accepted: 2026-11-14

`Droschinsky2018.BoundaryStates.StateValid` specifies a concrete common-root
pair inside descendant subtrees with fixed input orientations. `stateScore`
adds exactly the boundary skipped-vertex penalty to the independent internal
vertex/path score. The mapped boundary has no additional penalty.
`StateValid.skipped_cover`, `extend_left` / `extend_right` and
`stateScore_step_left` / `stateScore_step_right` prove both child-descent
directions with exactly one penalty, including the infinite-penalty case.

`SkippedRecurrence` defines finite independent mapped/skipped witness maxima.
`allStateValue_eq_max` proves their exact partition; `skipped_recurrence_two_state`
proves the diamond half of 2018 Lemma 5 against those independent optima,
including empty child families. The mapped-root matching half, executable DP,
optimized matching/cost and actual graph Rust refinement remain open.

## Common-tree graft foundation accepted: 2026-11-14

`Shared.TreeGraft.tree` constructs a common tree by attaching a fresh root
to the specified roots of any finite family of finite trees. Its carrier is
`Option (Sigma A)`, keeping branch vertices distinct. `edges_card` proves the
exact edge count, and `isTree` derives the tree invariant from Mathlib's
connectivity/cardinality criterion. `root_path` and `child_cases` prove the
actual canonical root paths and complete rooted-child classification.

This supplies the common-tree constructor for 2018 mapped-state witness
assembly. Admissible ambient realization gluing and the mapped-state matching
recurrence remain open.

## Ambient embedding assembly accepted: 2026-11-14

`Shared.GraftedEmbedding.embedding` constructs a source-style rooted embedding
of the grafted common tree from independently valid branch embeddings placed
in distinct immediate input-child regions. Injectivity, parent-to-child ancestry,
and exact branch-path intersections are derived from those concrete hypotheses.
`TreeGraft.child_from_root` / `child_from_branch` provide the actual child cases;
`RootedFork.child_paths_intersection` proves distinct input regions meet only
at their parent. This supplies the structural assembly direction for a mapped
2018 state. The score identity, matching optimum and full mapped recurrence
remain open.

## Mapped-branch score identities accepted: 2026-11-14

`Droschinsky2018.realizationScore_graft` proves the exact abstract-tree score
of a graft: the parent vertex once, one connecting path pair per branch, and
each branch's internal score once. `connecting_path_score` proves that the
connecting path is direct exactly when the common branch root is the immediate
input-child pair. `connecting_reward_boundary` equates its complete reward
with the mapped edge-plus-boundary value in that case and the skipped boundary
value otherwise. Longer paths consult no edge reward or compatibility.

These identities include infinite penalties and signed/bottom weights.
Combining finite branch witness choices with optimal matching, proving the
full mapped-root recurrence, evaluation/optimization and Rust refinement remain open.

## Concrete mapped-parent assembly and branch optima accepted: 2026-11-14

`StateValid.pointed` realizes a boundary witness with its specified top pair
as the explicit common root, preserving every mapped pair and its complete
internal score. `BoundaryFamily.state_valid` constructs the actual parent
mapping from any injective child matching and valid boundary continuations;
`score_eq` and `boundary_score_eq` prove its full score exactly.

`matchingBranchValue_attained` proves each derived child-matching weight is
attained by an actual boundary witness; `connecting_reward_le_branchValue`
proves the opposite bound on every independent continuation. Mapped-state
maxima always have witnesses, including bottom scores. Skipped maxima are
used only when non-bottom, so empty skipped families do not acquire invented
witnesses. The full mapped-state recurrence still requires optimal matching
assembly and decomposition of arbitrary mapped-root witnesses.

## Optimal child matching assembly accepted: 2026-11-14

`Droschinsky2018.familyOfMatching_score` constructs a concrete parent mapping
for every compatible partial child matching, selects actual attaining branch
witnesses and proves its score equals the node-plus-matching objective.
`bestStateMatching_correct` certifies the finite matching oracle, and
`matchingValue_le_mappedValue` proves optimal matching assembly is bounded by
the independent mapped-state optimum. This is the constructive lower-bound
direction of the mapped recurrence. Decomposition of arbitrary mapped-root
witnesses is still needed for the reverse inequality.

## Arbitrary common-tree score decomposition accepted: 2026-11-14

`RootedDecomposition.iso` gives an explicit graph isomorphism from the graft
of a finite tree's child-descendant regions back to that tree. Flattening is
bijective and preserves/reflects actual adjacency. `pairedImage_precomposeIso`
and `realizationScore_precomposeIso` preserve vertex pairs and scores under
this reindexing. `ScoreDecomposition.score_decomposition` therefore proves
the complete root/branch score partition for every independent explicit
common-tree realization, rather than only for assembled witnesses.

The remaining mapped-recurrence direction must assign these common-child
branches injectively to immediate input-child pairs and bound their rewards
by the certified child matching optimum.

## Full 2018 two-state recurrence accepted: 2026-11-14

`RootedTopologicalEmbedding.branchChild_injective` assigns distinct common
children to distinct immediate input-child regions. Restricting the actual
common-child regions produces valid independent boundary witnesses.
`MappedDecomposition.source_score_upper` bounds every source-style witness
by the certified child matching optimum, using the exact arbitrary-tree score
partition. `mappedValue_le_matchingValue` proves the reverse mapped inequality.

`mapped_recurrence` together with `skipped_recurrence_two_state` proves both
halves of 2018 Lemma 5 against independently optimized concrete witnesses,
with signed/negative-infinity weights and finite/infinite penalties. These
are Bellman identities; continuation values remain finite witness optima and
the matching oracle remains exhaustive. Executable recursive evaluation,
optimized matching, cost bounds and actual graph Rust refinement remain open.

## Overall objectives and rooted evaluation order accepted: 2026-11-14

`Droschinsky2018.rootedValue_eq_max_mapped` equates the independent rooted
source optimum with the largest mapped-state entry in the supplied orientations.
`unrootedValue_eq_max_rerooted_mapped` proves the straightforward unrooted
baseline that tries every root pair. Both preserve nonempty negative/bottom
optima and charge no boundary skips above the chosen common root.

`Shared.RootedEvaluationOrder.wellFounded` derives the rooted recurrence order
from actual canonical path depths and their finite maxima. One-child and
two-child dependencies strictly decrease the rank. This discharges rooted
termination/order without a supplied DAG hypothesis. It does not establish
the optimized unrooted matching-reuse order or any computation's time bound.
Executable evaluation, optimized matching, numerical/Rust refinement and the
published cost theorems remain open.

## Executed independent evidence

- All 197 rooted ordered trees through six edges agree between independently
  enumerated tree contractions and matched-pair deletions.
- Lemma 8's numerical recurrence agrees with operational optima on 19,503
  unordered pairs from those trees. It disagrees with the literal printed
  objective on 7,554 pairs. This is finite evidence, not a general DP proof.
- The latest Python test suite passes 65 tests, with three tests skipped.
- The graph-only Rust crate passes 39 tests, including an exhaustive
  partial-injection embedding oracle with independently reconstructed paths
  and scores. This tests signed weights and forbidden edge labels.
- Both 2018 discriminator cases return 1.75 in Rust and Python. Skipped paths
  have no edge reward and do not require edge-label compatibility.
- Charon/Aeneas generated the maintained Lean operation from Rust; the
  regeneration comparison passes and the generated module and refinement
  theorem compile. The standalone Rust extraction crate compiles and its
  Cargo test command succeeds, including the six-edge contraction oracle.

## Actual shared potential updates with sparse feasibility: 2026-11-14

`Rust.SparseAssignmentAdjustment.adjust_potentials_sparse_safe_spec` extends
the existing actual Rust `adjust_potentials` routine to sparse allowed-edge
feasibility. Its physical vector writes, resulting feasible dual, component
envelope, objective accounting and reserved-zero value are proved. Every
checked addition/subtraction bound is derived from the sparse cut minimum,
allowed-edge cost bounds, compatible perfect-assignment existence and the
independent search/envelope invariants. Machine-operation success or an arbitrary
per-operation fit certificate is not a premise.

The proof reuses the actual complete array-update refinement and replaces the
dense weak-duality budget by the independently proved sparse budget. No Rust
code change or second unverified potential updater is needed. This presently
uses the exact reference's envelope relative to zero initial column potentials;
the paper's larger-side initialization has nonzero copy-column potentials and
still needs the corresponding two-sided baseline envelope. The full sparse
search/caller, initialization/deletion state construction and fast costs remain
open. This is a source component theorem, not a complete sparse solver claim.

## Actual Rust allowed-cut minimum and sparse dual bridge: 2026-11-14

The exact assignment crate now has `sparse::minimum_sparse_cut`, a checked
optional-edge cut primitive. Its real Rust source validates the square matrix
and all state-vector lengths, rejects oversized extents, scans only selected
rows/unselected columns with present edges, and returns an original attaining
row/column and exact i128 reduced cost. Absence means no allowed crossing edge;
checked arithmetic errors remain explicit. It is a full-matrix reference scan,
not the paper's sparse priority-queue repair algorithm.

`Rust.SparseCut.minimum_sparse_cut_edges_spec` proves safe terminating exact
original-edge minimum selection for every represented input in its explicit
shape/size/potential frame: matching square dimensions, extent at most u32 MAX,
and potentials in [-2^96,2^96], the uniform exact-assignment state envelope.
The source selector, shape loop, row loop, both checked subtractions, outer
loop and original-coordinate readback are proved from extracted source.
The minimum is related to an independent candidate enumeration and then to
actual optional graph edges; no attaining edge or minimum certificate is supplied.

`minimum_sparse_cut_adjustment_spec` additionally consumes the independently
stated sparse APM invariants: feasible duals, a one-excess-row alternating cut
and existence of a compatible perfect assignment. It rules out an absent cut
and proves the actual returned delta is nonnegative, preserves the ideal
sparse dual update and creates a tight allowed edge. Physical potential-vector
updating, predecessor search, augmentation and the complete sparse solver remain
open. The theorem does not cover arbitrary unbounded i128 state vectors.

All eight exact-core tests pass, including 2,728 independent small cut-mask
comparisons through side four and explicit malformed/overflow/absent-edge cases.
Pinned extraction succeeds after factoring nested scans and copying an optional
entry before matching it; maintained generated semantics are regenerated from
source. No handwritten generated-code changes or new foreign operation model
were introduced. Full sparse repair and the paper time bound are not claimed.

## Sparse cut progress and numeric envelope: 2026-11-14

`AssignmentSparsePotentials.exists_allowed_crossing` derives a real allowed
edge across every alternating cut with more selected rows than columns from
one compatible perfect assignment. `exists_cut_adjustment_on` minimizes over
only actual cut edges, derives nonnegative attained slack, preserves sparse
dual feasibility and creates a tight allowed edge. Forbidden pairs receive no
finite replacement cost. Existing tight-edge preservation and one-excess-row
objective accounting apply to the same update.

`dualValue_le_card_mul_on` and `total_increment_bound_on` use sparse weak duality
and allowed-edge cost bounds to prove the dimension/cost envelope.
`ideal_adjustment_increment_bound_on` establishes the next cumulative bound
before any machine update is assumed representable. This extends the independent
numeric-safety argument used by the dense exact reference to the source sparse
APM setting. Executable sparse scans/search, priority-queue costs and the full
paper repair/refinement remain open.

## One-cycle optimal repair of the paper copied graph: 2026-11-14

`Shared/AssignmentCycleRepair` reuses Mathlib permutation cycles to prove the
one-augmentation structural argument independently of an implementation. A
completed near-perfect assignment has compatible tight old edges except at
one free row. Under a feasible sparse dual, replacing only the difference cycle
through that row costs no more than any compatible perfect replacement: all
other replacement cycles contribute nonnegative slack over old tight edges.
An independently optimal compatible assignment exists by finite minimization,
so `Assignment.exists_single_cycle_repair` derives an optimal one-cycle repair
without accepting an optimal replacement as an endpoint premise.

`AssignmentDeletedPermutation` bypasses the removed vertex in its original
permutation cycle, restricts to the actual surviving subtype and identifies the
unique temporary free-row/free-column edge. Every other old assignment edge
is unchanged. `CopiedMatchingRepair.matched_single_cycle_repair` instantiates
this with the actual paper graph, original feasible/tight potentials and a
matched original right vertex. Feasibility of the deleted graph is constructed
from its surviving identity-copy edges. It yields a global perfect optimum
changing only the one repair cycle, with all other old edges preserved.

This establishes optimal repair by a single alternating cycle; removing its
temporary completion edge gives the intended augmenting-path interpretation.
It does not yet implement the sparse path search, potential updates, fast
priority queue or the paper operation bound. Decoding the repaired induced-graph
optimum, executable repair and optimized source refinement remain open.

## Actual final-cache owned word payload: 2026-11-14

`Rust.GuidedReconstruction.maximum_common_embedding_indexed_guided_payload_of_trees`
proves a bound on the actual returned guided cache's complete owned key/result
word payload for every admitted original tree pair. `wordNodes` counts both
Pair and Empty constructors in a source word, exactly `2*pairs+1`.
`memoWordNodes` adds all three owned words in every actual cache record,
including repeated values across records.

For original edge/pair counts nL/nR, the final cache contains at most
`(2*(nL+nR+min(nL,nR))+3)*records` word constructors. Combining this with the
proved complete record bound gives the same coefficient times
`3*B(left)*B(right)`. The proof bounds every key in the full three-product query
family and uses actual cache soundness to bound each stored result by both
key words. It does not assume that equal word values share memory.

This is a structural size metric of the actual returned value. Table links,
record structs, allocator bytes, intermediate allocations and peak live memory
are excluded. Complete execution/copy/comparison costs and an efficient
representation remain open. The structural payload factor explains why a
record-count theorem alone is not a complete memory claim for this owned table.

## Actual guided-cache bound in original tree parameters: 2026-11-14

`ContractionMeasures` proves that independent edge contractions cannot increase
actual leaf count or root-to-leaf vertex depth, including contractions at
arbitrary depth and the singleton boundary. Context monotonicity and the
independent contraction closure supply both general measure inequalities.
Together with the proved edge inequality, they imply monotonicity of the
repaired decomposition bound
`B(T)=edges(T)*(min(depth(T),actualLeaves(T))+1)+1`.

`Rust.GuidedReconstruction.CorrectGuided.original_cache_bound` now bounds the
actual complete guided memo by `3*B(left)*B(right)`. The proof uses the actual
optimal output's independent contractions to bound its decomposition family by
each original input bound, then accounts for all three real query products.
`maximum_common_embedding_indexed_guided_cache_of_trees` covers every admitted
independent tree pair through the actual cache-returning Rust endpoint, with
only the input edge bounds. No output-size or free cache assumption is needed.

The cache record bound is now entirely in original tree sizes, depths and true
leaf counts. Stored owned-word payload size, structural comparison/copy costs,
intermediate allocation and full running-time bounds remain separate work.

## Actual combined guided-cache bound: 2026-11-14

The actual `maximum_common_embedding_indexed_guided_with_cache` entry point
returns the independently maximum original-index matching, its real final memo
and a u64 reconstruction-call counter. The ordinary guided entry point discards
this instrumentation and returns the same matching. Its compiled universal
source contract is
`Rust.GuidedReconstruction.maximum_common_embedding_indexed_guided_with_cache_spec`.
It derives all cache properties from the initially empty table, without a public
cache or optimum certificate.

For original words L/R and the actual returned shape P, the final memo has unique
keys contained in `D(L)×D(R) ∪ D(P)×D(L) ∪ D(P)×D(R)`.
`CorrectGuided.cache_bound` consequently bounds the actual number of records by
`|D(L)|*|D(R)| + |D(P)|*(|D(L)|+|D(R)|)`. The actual total recorded reconstruction
calls are at most `2*(pairs(L)+pairs(R))+2`, including both sides and with checked
u64 safety derived. This closes the missing feasibility-cache family observed
in the indexed benchmark; the initial optimizer's single product was insufficient.

`MemoGrowth` composes actual numerical memo growth and key uniqueness across
query families. `GuidedCacheGrowth` proves every actual guard and recursive
helper only adds its enclosing pattern/input decomposition product. The final
source proof conjoins this independent growth theorem with complete functional
reconstruction and composes the original optimization plus both real witness
runs. The returned pattern is not assumed to be an original decomposition state.
This bounds stored records, not total allocation, structural word copies, cache
comparison work or wall-clock time. A bound solely in original tree parameters
and a complete representation/dictionary cost theorem remain open.

## Guided/reference witness measurements: 2026-11-14

[The indexed witness benchmark](../../dev/benchmarks/2026-11-14-indexed-witnesses.md)
records 150 samples across ten chain, star, balanced, broom, caterpillar and
unequal-size cases, with separate full-reference, full-guided and guided-witness
phases. All 30 case/mode processes have CPU time and peak RSS records excluding
Cargo/compilation. Compiler/profile, hardware, warmup, measured phase boundaries
and variability are documented. Guided full-run medians are approximately 0–16%
slower here; these cases do not demonstrate a speedup. The recorded linear
witness-call counts hold, while shape-dependent memo entries and structural
costs dominate. Chain/star guided feasibility adds a cache entry, demonstrating
why the initial optimizer's D-product cache proof alone cannot cover the whole
guided wrapper. Combined cache/copy costs and allocation instrumentation remain
open.

## Actual guided indexed reconstruction and linear witness calls: 2026-11-14

`Rust.GuidedReconstruction.reconstruct_guided_spec` proves total correctness of
the actual new `guided::reconstruct_guided` on every represented pattern/input
below 2^32 pairs with a sound shared memo. The output is a genuine indexed
contraction of exactly the requested shape, or independent infeasibility. The
actual u64 source counter is at most `2*input_pairs+1`; all checked counter
arithmetic is derived safe, and the output memo remains sound.

The actual guard runs the already proved memoized optimizer and structural
word equality. `EmbeddingFeasibility.paperCommon_eq_left_iff` establishes
independent feasibility from that equality, using strict contraction size and
optimum completeness. `GuidedFeasibility` proves actual shape erasure and both
retention guards, including memo threading. The source chooses retention only
when both subpatterns embed; a rejected branch builds no recursive witness.

`maximum_common_embedding_indexed_guided_of_trees` composes actual optimization,
canonical original numbering and guided reconstruction into an independently
maximum indexed tree for every admitted original tree pair. The flat-token Rust
API and its opt-in Python backend now use this guided entry point; their total
correctness/readback/forest-optimum theorems continue to compile. The older
backtracking entry point remains a separately proved reference.

The native oracle compares old and guided reconstruction on all 38,809 pattern/
input pairs through six edges, including feasibility, exact original retained
identities and the recorded call bound. Both public indexed optima have identical
original-index witnesses and scores on all those pairs, and the flat-token oracle
passes with the guided implementation. The full library builds (3,660 jobs), regeneration matches both maintained
crates, and all 91 Python tests pass with the rebuilt guided extension.
The linear bound counts witness calls,
not feasibility memo work, table scans or shape copies. Combined key-space,
allocation and complete running-time bounds remain open; no paper runtime is
claimed for this implementation.

## Vertex-root forest convention and actual Rust optimum: 2026-11-14

The independent ordered-forest relation now lives upstream of the Dyck encoding
in `Paper2004/OrderedForest.lean`. A forest step deletes a vertex and promotes
its children, including at component roots, or contracts inside a component.
`forestEmbeds_iff_parent` proves exact two-way correspondence with ordinary tree
edge contractions after attaching one retained virtual parent. The independent
`IsMaximumCommonForest` counts actual original forest vertices, including
component roots; `isMaximumCommonForest_iff_parent` proves its exact optimum
correspondence with the virtual-parent tree.

`VertexEncoding` explicitly identifies the one-pair-per-vertex forest encoding:
a single tree has an additional outer pair around its paper edge encoding;
each original vertex contributes two tokens, and the virtual parent contributes
none. `maximumTokenEmbedding_vertices` transfers exact original-array readback,
ordered retained token positions and global optimality to this independent
forest contract. `Rust.TokenMatching.maximum_common_token_embedding_of_forests`
composes that bridge with the actual extracted Boolean Rust API for every
represented forest input with fewer than 2^32 original vertices.

Five Python/NetworkX regression cases cover singleton roots, branching/chain
comparisons, disconnected forests, deletion of an internal branching vertex,
exact vertex scores and retained original graph-node identities. They pass
against the opt-in backend. This proves the mathematical vertex/root convention
and the actual Boolean source call under that representation. Python DFS token
construction, graph-node marshaling and reconstruction remain tested conversion
boundaries, not a source-refinement theorem about NetworkX internals.

## Opt-in Python integration of the proved Boolean core: 2026-11-14

`longest_common_balanced_embedding(..., node_affinity=None, impl="verified-rust")`
now calls the proved `verified_ordered_core` through a thin PyO3 index-list API.
The Python shim fully validates original typed bracket pairs before Boolean
erasure and reads the returned positions from the original strings, tuples or
lists. Non-unweighted affinities are explicitly rejected. Automatic dispatch
and ordinary affinity-capable discovery are preserved; opt-in discovery uses
`include_restricted=True`. Absent or older optional extensions are handled
without registering an unavailable implementation.

All 86 Python tests pass with the locally built extension. Nineteen new boundary
tests include empty inputs, typed mismatches, integer tokens, original container
values, explicit affinity rejection, raw FFI errors/indices and exhaustive
comparison over all balanced words through four pairs. The CMake/scikit-build
wheel builds with Rust required and Cython disabled; its 23 new/existing Rust
backend tests pass from `/tmp` against a separate target installation. CI now
includes that installed-package path. The extension lockfile adds only the
local core dependency, preserving existing registry pins, and CMake tracks its
Rust source dependencies.

This is tested Python/PyO3 integration of the formally proved Boolean API.
Python token conversion, extension marshaling and NetworkX vertex/root encoding
are outside the existing Lean source theorem. General affinities, efficient
witness reconstruction and the paper runtime remain open for this new backend.

## Actual flat-token optimum and retained-token witnesses: 2026-11-14

`Rust.TokenMatching.maximum_common_token_embedding_total_spec` proves total
correctness of the actual public `maximum_common_token_embedding` Rust API on
every represented pair of Boolean token slices. Independently balanced inputs
with fewer than 2^32 pairs succeed; excluded inputs return their original parser
error with left-input precedence. Internal solver/index errors are unreachable.

Success satisfies `Paper2004.TokenEncoding.MaximumTokenEmbedding`: both actual
output index lists are ordered sublists of the original full token ranges;
reading them from the original inputs spells exactly the same balanced word;
that word attains the independent tree-contraction optimum with its exact pair
score. Distinctness, bounds and two returned tokens per scored pair follow from
this contract. No input parser, optimum or index-validity certificate is a public
endpoint premise.

`CanonicalTokenPositions` proves the exact canonical original pair-coordinate
table expands to the complete original token range. `TokenReading` proves
original-array readback survives arbitrary indexed pair deletions. The actual
`emit_tokens` refinement derives all source casts, coordinate reads and output
capacity bounds from parser correctness and indexed retention, then composes
with the actual memoized optimizer and complete reconstruction proofs.

The native oracle tests the flat API on all 38,809 pairs of the 197 ordered trees
through six edges against independent arbitrary tree-contraction closures,
checking exact score, both readback sequences, original ordering and lengths.
All eight ordered-core integration tests pass. Source extraction is regenerated
from the maintained Rust. This remains an unweighted Boolean reference adapter:
backtracking witness reconstruction has no paper running-time claim. Typed
external tokens, Python/NetworkX conversion, optimized reconstruction and full
implementation costs remain open.

## Actual flat-token parser total correctness: 2026-11-14

`Rust.TokenParser.parse_balanced_tokens_total_spec` proves the actual public
Rust parser safely terminates on every represented Boolean token array.
Acceptance is exactly the independent Dyck encoding with fewer than 2^32 pairs.
Success returns the whole original shape, a counter exactly at input end and
precisely the independent original opening/closing coordinates in preorder.
Every returned source error excludes that independent admitted domain; no
out-of-bounds read/write, arithmetic failure or divergence is admitted by the
contract. `parse_balanced_tokens_spec` gives admitted-input success directly.

`parse_forest_accepted_spec` proves exact contents against independent encoded
segments and `positionPairs`, including preservation of previous coordinates.
Actual pushes and the mutable closing-position read/backward update are
verified. A separate `parse_forest_total_spec` proves safety, consumed-substring
soundness and bounded coordinate counts for arbitrary malformed segments using
strict advancement of the actual token counter. The public proof combines
universal shape soundness with exact accepted-input contents, ruling out false
acceptance and erroneous rejection without assuming a parsed tree or table.
All machine bounds and threshold casts are derived, including both supported
pointer widths and empty input.

The full maintained library builds successfully (3,648 jobs). The Rust source
is unchanged from the exhaustive stack-oracle tests and pinned extraction
comparison. This completes the flat Boolean parser refinement under
the existing supported-operation/allocation model. Actual retained-token
emission, composition with indexed optimization, typed token/NetworkX conversion
and optional backend dispatch remain open.

## Original token coordinates and flat-input parser prototype: 2026-11-14

`Paper2004.IndexedWord.tokenIndices` emits each retained pair's actual opening
coordinate, interior, closing coordinate and suffix. The independently defined
indexed deletion relation preserves an ordered sublist of both original token
coordinates (`Retains.tokenIndices_sublist`), including deletion of both tokens
at arbitrary depth. Distinctness and actual token-array bounds transfer from
the original coordinate stream, with exactly two token coordinates per scored
edge. This is separate from the already verified zero-based pair identities.

`Paper2004.TokenEncoding` specifies the flat Boolean alphabet (`false` opens,
`true` closes), its injective correspondence with the existing Dyck language,
and exact token length. `positionPairs` independently specifies original
opening/closing coordinates in preorder; its length and strict original-segment
bounds are proved.

The ordered Rust core now has a checked `tokens::parse_balanced_tokens`
prototype, with explicit unmatched-open/close and pair-count errors, and an
owned preorder coordinate table. An independent stack oracle tests every one
of the 32,767 Boolean words through fourteen tokens, checking acceptance,
complete returned shape and every opening/closing coordinate. All six ordered
crate tests pass, including the earlier exhaustive indexed-optimum oracles.
The full maintained library builds successfully (3,643 jobs), and fresh pinned
extraction matches both maintained generated modules. The parser parameter is
named `input` to avoid a generated Lean module/local-name collision. This parser has not yet been
refined in Lean; exact source parsing/coordinate proofs, token-index emission,
PyO3/NetworkX conversion and dispatch remain open. It is not a default backend.

## Actual public original-index LCBE optimum: 2026-11-14

`Rust.IndexedOrderedSolver.maximum_common_embedding_indexed_of_trees` proves
successful termination of the actual public indexed Rust entry point on every
pair of independently specified ordered trees with fewer than 2^32 edges each.
Its result satisfies the independent `Paper2004.IndexedWord.IndexedMaximum`
contract: actual pair deletions from both exact canonical originals, identical
surviving shape, independently maximum common contracted tree and exact score.
`maximum_common_embedding_indexed_indices` additionally states distinct genuine
input indices in bounds, with one original pair identity on each side for every
scored output edge. The identities are zero-based opening/preorder *edge/pair*
positions; token-position and NetworkX vertex conversions remain separate.

`CanonicalIndexedWord` defines numbering on Mathlib binary trees, independently
of Rust. `number_word_refines` is strengthened to identify the actual numbered
model exactly with this canonical representation, not just an arbitrary shape
and valid-looking range. The public proof composes the already verified actual
memoized optimum, both actual checked numberings and complete reconstruction.
Every local range and reconstruction-success obligation is derived; no caller
supplies an optimum, index mapping, path or reconstruction certificate.

The full maintained library builds successfully (3,641 jobs). Independent
labeled-contraction tests and the pinned extraction comparison passed after
the final Rust source change. This completes original edge-index
witness refinement for the LCBE reference API. Reconstruction is backtracking,
so the memoized shape table-count theorem does not establish a polynomial or
paper running-time bound for the indexed wrapper. Efficient indexed witness
reconstruction, ordered-isomorphism indices, token/vertex adapters and complete
qualified performance evidence remain open.

## Actual indexed reconstruction total correctness: 2026-11-14

`Rust.IndexedOrderedSolver.reconstruct_embedding_refines` proves every actual
Rust reconstruction call terminates, with no feasibility or size premise.
Success returns a witness in the independently defined indexed `Retains`
relation and erases to exactly the requested pattern. Failure proves the
pattern independently infeasible under tree/Dyck contraction semantics.
`reconstruct_embedding_success` rules out failure for every feasible pattern;
`reconstruct_embedding_none_iff` gives the exact rejection equivalence.

The proof handles both early failure branches and their actual copied/spliced
fallback input. The structural `must_drop_first` lemma derives fallback
completeness from independent first-pair decomposition and uniqueness of the
pattern interior/suffix. A well-founded input/pattern semilength measure proves
termination of every generated partial-fixpoint call. It neither redefines
containment by the algorithm nor supplies a presumed reconstruction witness.
The copy/append source proofs preserve actual pair identities throughout.

Composition with the actual memoized optimum and exact canonical original
input numbering remains open for the public indexed entry point. The source
has not changed since the exhaustive labeled-contraction tests and pinned
extraction comparison passed. No optimized reconstruction-cost claim follows.

## Actual Rust original-index numbering and structural helpers: 2026-11-14

The ordered extraction crate now includes `indexed::maximum_common_embedding_indexed`:
a tested/extracted reference that selects the already verified memoized optimum
shape, numbers each original input independently, and reconstructs indexed
contraction witnesses. Labels are zero-based opening/preorder pair indices,
not Python vertex-pair token positions; the implicit tree root has no incoming
pair. Reconstruction is explicit backtracking with no optimized cost claim.

`Rust.IndexedOrderedSolver.copy_indexed_correct` and `append_indexed_correct`
prove actual source helpers preserve all identities and structure.
`number_word_refines` proves actual checked preorder numbering terminates,
keeps the entire original shape, assigns precisely `List.range' next count`,
and returns exactly `next+count`. Its only size premise is that this sum fits
the specified u32 range; every local checked addition is derived to succeed.
The model uses the independent Mathlib indexed-word specification.

Independent Rust tests enumerate arbitrary actual labeled tree contractions.
For every pair among all 197 ordered trees through six edges, they check
reconstruction existence/nonexistence for the requested shape and exact retained
identities, plus both public indexed optimum witnesses and their scores.
Separate offset tests cover u32::MAX success/overflow boundaries. All four
ordered-core tests pass, including previous embedding/memo and isomorphism
oracles, and pinned extraction succeeds for both crates. Actual reconstruction
soundness/completeness and the public indexed optimum refinement remain open.

## Independent original-index witness contract: 2026-11-14

`Paper2004.IndexedWord` uses Mathlib binary trees whose nodes carry original
matched-pair indices. Its `Step` deletes a pair at an arbitrary structural
context and splices the indexed interior before the suffix. `Retains` is the
operational closure, independently defined without the reconstruction solver
or erasure. `Retains.erase_embeds` and `tree_embedding` prove this witness
refines the established independent Dyck/tree contraction relation.

`Retains.indices_sublist` proves deletion retains original identities in their
original opening/preorder order. `indices_nodup` preserves uniqueness, and
`index_lt` derives actual original-index bounds under canonical zero-based
numbering. Mathlib's `BinaryTree.numNodes` counts represented pairs;
`erase_semilength` and `indices_length` identify it with both unlabeled edge
score and indexed-list length. The indexed concatenation and context lemmas
preserve nesting and every retained identity.

This establishes the independent indexed-witness contract. Actual Rust input
numbering, reconstruction, completeness and composition with the verified
optimal shape solver remain open. Reconstruction must recover identities from
each original input after shape memoization, because equal cached shapes may
occur at different original indices.

## Actual Rust ordered-isomorphism reference solvers: 2026-11-14

The maintained extraction crate now implements separate root-preserving and
arbitrary-root isomorphism reference recursions in `src/isomorphism.rs`.
`Rust.OrderedIsomorphism.rooted_common_isomorphism_of_trees` and
`largest_common_isomorphism_of_trees` prove actual source success, independent
maximum ordered subtree witnesses and exact u32 edge scores for every pair
of independently specified ordered trees with fewer than 2^32 edges each.
The generated partial-fixpoint functions are proved to terminate, and both
checked candidate additions are proved to fit from independent subtree bounds.
No optimum, path or arithmetic certificate is supplied as an input.

`OrderedIsomorphismRepresentation.toForest_decode` and `toTree_decode` connect
the actual structural first-child/next-sibling representation to the existing
two-sided tree/Dyck bridge. Both source recursions return precisely the
previously verified witness computations, including their tie choices. An
independent Rust oracle enumerates whole-child selections in actual trees,
then all actual descendant roots. Both isomorphism solvers pass witness and
score checks on all 38,809 pairs of the 197 ordered trees through six edges.
The earlier embedding/memo tests still pass; pinned extraction succeeds for
both maintained crates.

The full maintained library builds successfully (3,621 jobs), and fresh pinned
source extraction exactly matches both committed generated modules.

These are exponential reference recursions, with no memoization or paper
running-time claim. Existing Python/PyO3 vertex-pair sequence APIs remain
separate: their outer forest can have a virtual root. Original input-index
maps, those conversions, efficient memo/dictionary costs and full integration
remain open. The supported-operation/allocation boundary is unchanged.

## Independent ordered-isomorphism optima: 2026-11-14

`OrderedIsomorphism.lean` specifies adjacency-preserving ordered subtree
selection independently of sequences, contractions and algorithms. `RootPrunes`
and `ForestPrunes` delete whole child subtrees and independently prune retained
children in order. `IsomorphicSubtree` permits the selected root to be any
actual descendant. The root contributes no incoming virtual edge. This is a
separate project extension; the 2004 paper proves its LCBE contraction
recurrence and does not state this second isomorphism recurrence.

`OrderedIsoDP.level_correct` proves a constructive root-preserving common
optimum. `anywhere_correct` proves a constructive maximum common connected
ordered subtree with freely chosen roots. Soundness and completeness are
structural proofs against the independent relations, with edge counts bounding
all recursive calls. Separate numeric computations have independent optimum
theorems `levelSize_optimum` and `anywhereSize_optimum`, and exact witness-score
agreement. Neither optimum is defined by its algorithm.

Six kernel-checked cases in `Tests/OrderedIsomorphism.lean` distinguish fixed
and arbitrary roots and prove a contraction/isomorphism separation: contracting
an internal edge can produce a three-leaf star, whereas adjacency-preserving
selection has optimum two on the same inputs. Vertex-pair sequence APIs may
represent a forest at their outer level; correspondence to those existing APIs,
actual Rust refinement, index reconstruction and efficient memo costs remain
open for this extension.

## Outstanding obligations

| Target | State |
| --- | --- |
| Fresh-checkout local reproduction | Passed from `git archive 6dbf81e` on local disk with a fresh `.lake`; `lake exe cache get && lake build` fetched pinned dependencies and built 3,473 jobs |
| First remote CI run | Pending; workflow added |
| Pinned source statement ledgers for all three papers | Added `docs/planning/paper_statement_crosswalk.md`; open source results are explicit |
| Paper D/R/S and actual tree-parameter state bounds | Proved, including `states_closed` / `states_least` for Definition 4 |
| Lemma 8 recurrence optimum and tree witness | Proved; actual Rust indexed LCBE reference returns exact original edge/pair identities, independently maximum tree and score; efficient reconstruction and token/vertex conversion remain open |
| LCBS/isomorphism's distinct ordered contract and optimum | Independent rooted/arbitrary-parent optima and complete structural, indexed and token Rust reference APIs proved; Python/PyO3 vertex conversion and optimized production source refinement open |
| Computation-specific complexity | Memo operation and association-list comparison counts proved; full structural/dictionary cost and Theorem 3 runtime still open |
| Translated Rust ordered solvers | Reference and owned-memo entry points proved, including updated-cache refinement and state bound; indexed/token LCBE and isomorphism reference paths proved; efficient dictionary/bit cost and Python/PyO3 conversion remain open |
| Hungarian/assignment reduction and actual Rust matching correctness | Exact signed ordered-ring dummy reduction and actual square signed-i64 assignment and rectangular optional signed-i64 partial-matching public APIs total correctness proved; graph integration, floating arithmetic equivalence and complexity open |
| 2016/2018 graph/path specifications | Nonempty unrooted witnesses, real/negative-infinity scores, finite optima and 2016 induced-isomorphism bridge proved; 2016 fixed-root Lemma 2 proved; 2016 rooted matching Eq. (1) and 2018 unrooted source correspondence proved; fixed ambient-root states and both 2018 boundary recurrences proved; executable rooted 2018 score evaluator proved; optimized algorithms and actual Rust graph refinement open |
| Verified Python adapters and qualified performance evidence | Open |

The overall program remains active. These results do not complete the paper
formalizations, published optimized algorithms, or end-to-end Rust graph verification.











## Sparse copied-graph duality and tight normalization: 2026-11-14

`AssignmentDualityOn` proves independent weak duality and feasible/tight
optimality with inequalities restricted to actual allowed edges. Compatible
permutations must respect that relation, so forbidden edges need no finite
sentinel. `tight_of_cost_eq_dual_on` proves the converse equality criterion:
nonnegative selected-edge slacks sum to zero only when every selected edge is
tight. `tight_transfer_on` preserves tightness for any equal-cost compatible
replacement under the same dual.

`CopiedAssignmentReduction.feasible_tight_decodes` connects the paper's
maximization dual convention to this independent sparse assignment criterion
and yields maximum original and copy matchings. `normalize_tight` replaces a
compatible tight optimum by the involution swapping just its decoded original
pairs. The normalized assignment has exactly the same weight, stays compatible
and tight under the original potentials, and pairs every unused right vertex
to its own copy. This justifies the unmatched/matched deletion split even if
the old assignment used zero-weight cross edges or its two decoded components
differed. The original optimum is proved from duality; it is not a supplied
premise of the normalization theorem.

These are mathematical certificates and normalization proofs for the source
construction. They do not replace verification of computing those certificates:
optimized sparse augmentation, its actual Rust refinement and runtime bounds
remain open. The actual reference matching/deletion-family public APIs already
have separate unconditional admitted-input total-correctness proofs.

## Paper copied-graph dual and initial tight matching: 2026-11-14

`CopiedAssignmentReduction.initial_dual_feasible` proves the exact row-maximum
source initialization feasible. `rowMaximum` is the least bound on zero and
all finite row entries; including zero explicitly defines the all-forbidden,
all-negative and empty-row cases. Original left vertices and their copies
receive that row maximum, while right vertices and their copies receive zero.

`initialPairs_valid`, `initialPairs_tight` and `initialPairs_card` prove the
source right-identity edges form a compatible tight matching with exactly
|R| edges. `initial_edge_deficit` derives the |L| deficit; choosing the smaller
side as L gives the paper's augmentation count once a correct augmentation
routine is supplied. `deletion_preserves_dual_feasible` also proves that old
dual values restrict unchanged to all source-allowed surviving edges.

The row-maximum, compatibility, cardinality, tightness and feasibility claims
are mathematical proofs for the source construction. Sparse augmentation,
its source refinement and operation bounds remain open; these results do not
assert that the reference Rust family already implements the optimized repair.

## Paper deletion repair's exact single-pair deficit: 2026-11-14

`AssignmentVertexDeletion` independently retains original perfect-assignment
edges after one row and one column are removed. If those endpoints were paired,
the remainder has cardinality n-1. Otherwise `one_pair_deficit` proves it is
exactly one edge short of a surviving perfect matching, not an assumed bound.
`row_unmatched_iff` and `column_unmatched_iff` identify the unique surviving
free endpoints. Compatibility holds in the induced deleted graph, and every
retained tight edge keeps its equality under the old potentials.

`WeightedMatching.CopiedAssignmentReduction.matched_deletion_ready` applies
this to the source graph when an original right vertex is matched by the
decoded matching. Its copy row and original column belong to different old
edges, so their removal leaves a compatible matching of size |L|+|R|-2 on
|L|+|R|-1 surviving vertices per side, with exactly identified free endpoints.
`deletion_preserves_tight` proves the retained-edge equality. `edgeWeight`
represents source-allowed edges with `Option`; original, reversed-copy and
identity-edge weight lemmas establish exact nonnegative/zero source weights.

These close the combinatorial deficit and tightness-preservation steps of
2016 Lemma 6. Existence/correctness of the optimized sparse augmentation,
restriction of feasible duals, initial larger-side tight matching, actual Rust
repair and the running-time bounds remain separate open obligations.

## Paper copied-graph assignment reduction: 2026-11-14

`WeightedMatching.CopiedAssignmentReduction` now specifies the exact copied
bipartite construction used by 2016 Lemma 5: nonnegative compatible original
edges, reversed copied edges with the same weight, zero identity copy edges,
and forbidden off-diagonal same-side pairs. Its perfect assignments differ
from those of the dense dummy adapter currently used by the Rust reference.

`assignmentWeight_split` and `assignmentWeight_decode` prove the doubled
objective equals the sum of the original and copy decoded matching weights.
`extend_allowed` constructs an actual allowed perfect assignment from any
nonnegative compatible partial matching. The empty matching always extends,
including empty sides. `IsMaximum.selected_nonnegative` proves dropping
negative edges is sound for every independent maximum. Using an independently
finite exhaustive maximum, `dominates_allowed_decodes` proves that any
assignment dominating all allowed perfect assignments decodes to independent
maximum matchings in both components. All statements are generic over the
ordered ring, including exact integers and reals, with no finite infinity
sentinel or supplied original-matching optimum premise.

This verifies the source copied-graph reduction, not its optimized execution.
The paper's initial dual/large-side tight matching, one-augmentation deletion
repair, sparse/rectangular Rust implementation and runtime bounds remain open.

## Actual public matching deletion-family total correctness: 2026-11-14

`Rust.MatchingDeletionEntrypoint.max_weight_matching_deletions_total_spec`
proves the complete actual public reference family API safely terminates on
every represented input. Admitted inputs return the original independently
maximum matching and every right-vertex-deleted optimum, with exact original
input-index pairs, unique pair lists and exact i128 weights. The original
shape/size rejection is preserved on every other represented input.
`max_weight_matching_deletions_spec` states admitted-input success directly.

`MatchingDeletionRepresentation` derives preserved row lengths, width,
admission and exact optional-integer model equality from the actual mask
construction. `MatchingDeletionCorrectness` connects detector membership to
independently matched right vertices, proves returned-result reuse sound, and
transports the already verified single-instance solver to each deleted graph.
`MatchingDeletionInvariant` proves every actual vector append preserves earlier
entries and their indices. The complete loop also proves that every unused
vertex's output is physically equal to the original matching result. All
counter, vector and mask operations are verified under the existing translation
and allocation model, with no supplied optimum or local arithmetic certificate.

The indexed result predicate is factored as `MatchingSolveBuiltMatrix.CorrectFor`
for an arbitrary independent finite weight matrix; `CorrectPartial` is its
original concrete-input specialization. The existing single-instance public
proof compiles unchanged in meaning after this factoring.

The full maintained library builds successfully (3,628 jobs). The Rust source
is unchanged from the tested and extraction-checked helper increment.

Matched deletions still run the full reference assignment solver. This proves
the whole reference family's functional behavior, not the paper's optimized
one-augmentation repair or its running-time bound. Graph integration and those
optimizations remain open.

## Deletion-family reuse foundations and actual helpers: 2026-11-14

`WeightedMatching.IsMaximum.deleteRight` proves the unmatched-vertex reuse
branch of 2016 Lemma 6 for independent optional signed/real weights: deleting
an unused right vertex preserves the original maximum and its exact score.
`valid_deleteRight_iff` characterizes surviving feasible pairs, and
`deletion_repair_card_bound` proves that potentially affected right vertices
number at most the smaller bipartition. `deletionFamily_correct` gives a
correct independent reference family that reuses surviving optima and
otherwise invokes the existing exhaustive optimizer. One-augmentation repair
and the source running-time bound are not established by these lemmas.

The exact Rust crate now implements `deletion::max_weight_matching_deletions`,
a tested/extracted reference family with original input indices. It reuses
unmatched results and fully recomputes matched deletions. Independent injection
tests validate all original/deleted witnesses and scores for 392 generated
matrices through six vertices per side, plus extreme/tie/malformed cases; all
six exact-core tests pass. `Rust.MatchingDeletionReuse.uses_right_spec` proves
the actual early-return detector exact, and `copy_matching_spec` proves actual
owned copying preserves all pairs and the weight. `MatchingDeletionMask`
proves both actual owned mask loops safely construct every specified cell,
preserving indices and dimensions. The full actual family wrapper and its
mathematical transport proof remain open, as do the optimized repair and costs.

## Actual public partial-matching API total correctness: 2026-11-14

`Rust.MatchingEntrypoint.max_weight_partial_matching_total_spec` proves the
actual public optional signed-i64 matrix API safely terminates on every
represented input. Rectangular matrices with dimension sum at most `u32::MAX`
and strictly below `usize::MAX` return an independently maximum compatible
partial matching. `MatchingSolveBuiltMatrix.CorrectPartial` identifies every
actual returned pair with its original input indices, proves list uniqueness,
and identifies the actual i128 weight with the independent matching weight.
Empty sides, forbidden edges, nonpositive weights, ties and extreme i64
weights are covered. The total contract gives precise `NonRectangular` and
`TooLarge` rejection conditions, including shape-before-size precedence;
assignment and arithmetic errors cannot occur on admitted inputs.
`max_weight_partial_matching_spec` states admitted-input success directly.

`MatchingAssignmentBridge` connects the actual square assignment and decoded
coordinates to the independent dummy reduction through Mathlib's finite sum
and permutation equivalences. `MatchingSolveBuiltMatrix.solve_built_matrix_spec`
composes the already verified public assignment with actual pair decoding and
a derived safe cost negation. The final wrapper proof verifies actual width
selection, shape validation, checked dimension sum, size checks and matrix
construction. No optimum, permutation, path or arithmetic certificate is an
endpoint premise. The proof has the same pinned translation, supported-operation
and allocation-model boundary as the square assignment core.

The full maintained library builds successfully (3,615 jobs), and pinned
source regeneration matches both committed generated modules. The existing
five Rust crate tests passed after the final source change.

This completes functional correctness of the exact partial-matching adapter.
Graph/Python integration, floating arithmetic equivalence, rectangular/reused
matching optimizations and their source running-time bounds remain open.

## Actual partial-matching validation and indexed decoding: 2026-11-14

The actual decoder now separates a borrowed single-pair helper from its owned
output-vector loop. `Rust.MatchingDecoding.decode_pair_spec` and
`decode_pairs_spec` prove safe successful execution and exact indexed-list
contents against an independent coordinate predicate: real left row, real
right column, actual assignment coordinate and strictly positive compatible
original weight. `MatchingDecodedWitness.mem_decodedPrefix` gives the exact
input-index membership relation, and `decodedPrefix_nodup` proves uniqueness
as a list property, so finite-set conversion cannot hide duplicate output.

`MatchingValidation.is_rectangular_spec` proves the actual shape validator
safely decides the independent width predicate, including empty sides and
early false returns. The existing Rust tests still pass after the helper
refactoring, and pinned source regeneration succeeds.

`Shared.AssignmentReindex.reindexed_assignment_decodes` uses Mathlib's index
and permutation equivalences to transport an independently feasible/tight
assignment into a globally maximum compatible partial matching, retaining
its exact negated-cost weight. This abstract bridge is now compiled; the
remaining concrete bridge must identify the actual decoder list and returned
score with that mathematical matching, then verify the public wrapper.
All four new maintained modules compile in the full library. No optimized
rectangular/reused matching runtime claim follows from this increment.

## Exact partial-matching adapter and actual cost construction: 2026-11-14

The exact Rust crate now provides `matching::max_weight_partial_matching` for
rectangular signed-i64 optional weights, with explicit shape/size errors and
an indexed positive-edge witness. Empty sides, forbidden and nonpositive edges
are handled by the independent |L|+|R| dummy-assignment reduction. Real right
columns occupy the second index block, matching the mathematical `Fin L ⊕
Fin R` convention. Independent tests cover 588 generated rectangular cases
through six vertices per side plus signed, forbidden, empty, malformed, tie
and extreme-i64 cases; all five crate tests pass, including the previous
320-case assignment oracle. Pinned extraction succeeds on the actual new
source, and the existing assignment public-API proof still compiles.

`Rust.MatchingCostSpecification.costAt_sum` identifies concrete array costs
with the independently proved ordered-ring dummy profit via Mathlib's finite
sum equivalence. `negative_profit_spec` proves actual signed negation safe
and exact. `MatchingCostConstruction.cost_cell_spec`, `cost_row_spec` and
`cost_matrix_spec` prove the actual helper and both owned-vector construction
loops safely terminate with every specified cell. `MatchingMatrixRepresentation`
derives actual row count, square shape, cell values and admission by the
verified assignment API from those constructed contents.

All three new maintained proof modules compile in the full library. Actual
pair-list decoding, its feasible maximum witness/score and the public partial
matching wrapper still need refinement proofs. Rectangular paper matching
optimizations and their running-time bounds remain separate open obligations.

## Actual public exact-assignment API total correctness: 2026-11-14

`Rust.AssignmentEntrypoint.min_cost_assignment_total_spec` proves successful
termination of the actual public Rust function on every represented matrix.
`ResultSpec` precisely distinguishes a globally correct assignment from the
source's size and shape rejections. Accepted input means a square signed-i64
matrix with dimension at most `u32::MAX` and a representable reserved extent
`n+1`. All accepted inputs return a result satisfying the independent
`AssignmentReturnedSpecification.Correct` predicate: a decoded permutation,
exact cost, exact exported potential lengths, feasible dual inequalities,
selected-edge tightness, primal/dual equality and minimum cost against every
competing permutation. `min_cost_assignment_spec` gives this admitted-input
success contract directly. Arithmetic and invariant errors are ruled out by
the total contract, including both extreme signed costs and empty input.

`AssignmentValidation.is_square_spec` verifies the actual validator on every
represented matrix, including early rejection with a real malformed row.
The public theorem composes actual size/cast/checked-extent validation,
row-minimum initialization, complete source driver and final decoding. Its
unsigned extent proof uses the pinned public checked-add alias theorem
without an additional private-body import. No minimum, path, local arithmetic
range or program-result certificate is an endpoint premise.

The full library builds with both maintained modules. This completes total
functional correctness of the square exact-integer assignment core under the
pinned translation/model boundary. The partial-matching adapter, graph/Python
integration, floating arithmetic equivalence, rectangular/reused matching
optimizations and implementation cost proofs remain open. The final opt-in
endpoint dependency review is still separate from routine compilation.

## Complete actual Rust assignment driver: 2026-11-14

`Rust.AssignmentDriverLoop.finish_assignment_spec` proves successful,
terminating execution of the actual complete assignment driver from actual
row-minimum initialization. The endpoint accepts represented square input,
the u32-sized dimension and reserved extent, and the exact initialized row
minimum vector; it assumes no optimum, selected path or local arithmetic
range certificate.

`AssignmentDriverInvariant` tracks exactly the rows covered before the current
row counter and proves the reserved-pointer write preserves all real entries.
`AssignmentDriverAugmentation` feeds the actual search's constructed ranked
tight forest into actual augmentation, extending unique row coverage and
preserving physical vector length and tightness. `AssignmentDriverBody`
verifies the entire source iteration and safe counter increment, while the
complete outer loop terminates at full independent row coverage. Actual
constant-vector contents establish its initial state.

`AssignmentReturnedSpecification.Correct` specifies the actual exported
permutation, exact integer cost, potential vector lengths, dual feasibility,
selected-edge tightness, primal/dual equality and global minimum cost against
every competing permutation. The actual final decoder establishes this
specification for the driver's returned data, including the empty assignment.
The full library builds with all six new maintained modules. The public
`min_cost_assignment` size/square validation still needs its own source proof
and connection to this driver; partial-matching/graph integration and the
remaining paper optimization and cost goals remain open.

## Complete actual Rust augmenting-column search: 2026-11-14

`Rust.AssignmentSearchLoop.find_augmenting_column_spec` proves successful,
terminating execution of the complete actual source search, including both
local vector initializers. It returns a positive real unmatched column,
preserves represented vector bounds, feasible numeric/objective invariants
and every old matching edge's tightness, and constructs a finite ranked tight
predecessor forest containing the returned column. Those forest properties
are exactly the input needed by the previously verified augmentation walk.

`AssignmentSearchInvariant` combines the independent partial-matching, cut,
numeric, discovery and edge invariants. `AssignmentSearchScan` derives all
actual scan ranges and availability and proves nonnegative attained cut
selection. `AssignmentSearchAdjustment` proves the complete actual adjustment
preserves the numeric, cut, matching and ranked tight-forest properties.
`AssignmentSearchTransition` establishes both initial and continuing states;
`AssignmentSearchBody` verifies every operation and guard of the actual running
branch. The loop terminates by strictly increasing the visit count below its
independently proved finite capacity. All source error branches are discharged
from the input/state invariants; no local overflow, selected minimum, path,
or program-result certificate is supplied to the public search endpoint.

The full library builds with all six new maintained modules. The actual
outer assignment driver must still connect search, augmentation, row coverage
and final reconstruction; its public entry point and validation remain open.
Partial-matching integration, optimized paper algorithms and implementation
cost goals remain open as recorded in the program plan.

## Discovery ranks and actual predecessor tightness: 2026-11-14

`Rust.AssignmentDiscoveryRanks` keeps visited discovery ranks below the visit
count and assigns that count to unvisited columns. Visiting the pending
column preserves strict predecessor descent; a selected unused column with
a visited predecessor extends the ranked terminal forest. Exact whole-table
frames prove the actual scan leaves every used predecessor slot unchanged.

`AssignmentVisitColumn` proves the physical boolean write inserts exactly
one candidate, increments the mathematical visit count, preserves nonzero
row pointers and the reserved flag, and restricts the previous cut invariant
to the remaining unused columns. It derives real row bounds for every
nonzero pointer from the independent unfinished partial assignment.

`AssignmentAdjustmentTightness.complete_matching_tight` derives matching
endpoint lockstep and proves tightness of every existing matching edge in the
actual returned potentials. Used predecessor edges remain tight through the
actual row/column writes, and an attaining predecessor at the selected unused
column gains zero actual reduced cost. `AssignmentPredecessorTightness`
combines those facts into visitation, actual scan and actual adjustment
preservation of tight predecessor forests.

The full library builds with these four maintained modules. These are the
rank and tightness components needed to assemble the complete actual search
loop; that assembly, the full driver and public entry-point theorem still
remain open. Later integration, paper optimizations and complexity goals are
unchanged.

## Derived actual search arithmetic and initialization: 2026-11-14

`Shared.AssignmentEnvelope` bounds each potential by the cumulative
nonnegative adjustment. Its ideal cut theorem establishes the new cumulative
bound from feasibility and dual progress before any checked machine update.
`Rust.AssignmentNumericBounds` specializes those bounds to signed i64 costs
and u32-sized dimensions, proving i128 representability of potentials, reserved
slot zero, reduced-cost subtractions, and finite slack subtractions.

`AssignmentSafeAdjustment.derived_adjustment_bounds` derives every local
arithmetic premise of the actual adjustment from independent cut and numeric
invariants. `AssignmentSearchArithmetic.PotentialInvariant` uses the negative
actual reserved column value as the cumulative adjustment; no new runtime
counter is introduced. `adjust_potentials_from_search_spec` proves successful
actual execution, preserves this invariant and all attained slack minima,
and derives every local checked-arithmetic range internally from those search
properties. It does not assume representability or success of the update
being verified. The actual complete-adjustment frames also preserve exact
objective/reserved-slot accounting.

`AssignmentSearchInitialization` defines initial rows as independent input
row minima, identifies the actual initialized vector with them, proves their
signed cost bounds, and establishes the initial potential, empty-candidate
slack and unused-column invariants from the actual initialized contents.
The full library builds with these five maintained modules. The actual
search loop still needs the combined discovery-rank, matched/predecessor
edge tightness and state-preservation proof; its full driver and public entry
point remain open, along with implementation cost and later program goals.

## Actual scan/adjust cut invariants and search capacity: 2026-11-14

`Shared.AssignmentSearchCapacity` derives the number of matched columns,
existence of a free column before completion, pointer injectivity including
the fresh row at reserved column zero, and finite visit capacity from the
independent partial-assignment specification. Its Rust bridge proves unused
free-column availability, the source's visit-counter guard, used-pointer
injectivity, and the exact candidate-set insertion induced by marking a
physical boolean vector slot.

`Shared.AssignmentSlack.MinimumAt` independently specifies an attained minimum
with infinity for an absent value. Candidate insertion preserves ties and
uniform finite subtraction preserves the attaining predecessor.
`Rust.AssignmentScanCut.scan_columns_cut_spec` proves actual successful
scanning extends this invariant by the active row. Its returned scalar is
attained by the physical stored predecessor and bounds every candidate reduced
cost across every unused real target. The precise whole-table scan frames
are retained. `AssignmentAdjustmentCut.complete_slack_invariant` proves the
actual returned potentials and slacks preserve all these attained minima.

`AssignmentCutFeasibility` derives nonnegative adjustment from feasible
potentials and an attaining candidate, converts actual candidate bounds into
the independent finite cut inequalities, and derives matching endpoint
lockstep from partial-pointer injectivity. These close substantive bridges
between the actual scan/adjust loops and search invariants. The complete
search loop still needs their initialization and preservation together with
discovery ranks and numeric envelopes; full driver and entry-point correctness
remain open. All six new maintained modules compile in the full library.

## Actual complete Rust assignment reconstruction: 2026-11-14

`Shared.AssignmentPointerDecoding.PartialRows.exists_permutation` derives an
inverse permutation from independent complete row coverage and injectivity;
`full_positive` proves no real column remains unmatched. The pointer tightness
specification connects to the existing finite assignment tightness criterion.

`Rust.AssignmentInverseReconstruction.reconstruct_inverse_loop_spec` proves
the actual first reconstruction loop safely writes the complete zero-based
inverse table and leaves its failure flag absent. The second actual loop,
`AssignmentCostReconstruction.reconstruct_cost_loop_spec`, returns the exact
independent selected-cost sum and precise real potential lists. Its arithmetic
proof bounds every selected-cost prefix by the count times 2^63; count at
most `u32::MAX` makes every actual checked i128 sum succeed, even at extreme
signed i64 costs. Arithmetic safety is derived rather than assumed for sums.

`Rust.AssignmentReconstruction.reconstruct_assignment_spec` combines both
actual loops. `reconstruct_assignment_minimum_spec` derives successful actual
reconstruction, exact cost and potentials, equality with the feasible dual
objective, and global minimum cost from independent complete pointer matching,
feasibility and matched-edge tightness. This verifies final decoding from
those input invariants, including empty assignments. Establishing them from
the actual alternating-tree search and full driver, deriving all search
arithmetic bounds, and cost refinement remain open. The full library builds
with the four new maintained modules.

## Actual Rust augmentation and partial matching: 2026-11-14

`Rust.AssignmentAugmentation.augment_matching_spec` proves successful,
terminating execution of the entire generated path walk, with exact vector
length and pointer values at every slot. A simple positive predecessor path
supplies the indexing and termination facts; its length bound is derived from
distinct indices in the represented dimension. `AssignmentPredecessorPaths`
constructs such a path from a local strictly decreasing discovery-rank forest,
retaining membership in that forest.

`Shared.AssignmentAugmentation.PartialRows` independently specifies unique
coverage of exactly the processed positive rows, allowing zero pointers at
unmatched columns. Its generic rerouting theorem extends coverage by the
fresh row. `Rust.AssignmentAugmentationPath` proves the input path reroutes
real columns bijectively onto the original columns with its unmatched head
replaced by reserved column zero. The actual vector frame connects that
combinatorics to `augment_matching_ranked_partial_spec`.

`augment_matching_ranked_tight_spec` combines actual successful execution,
matching extension and tightness preservation from tight predecessor-forest
edges. These are structural properties of the input matching and forest,
not certificates of the augmentation program's result. The full library
builds with all five new maintained modules. Establishing those forest and
tightness premises from the actual search, final decoding, numeric bounds,
entry-point correctness and implementation cost remain open.

## Complete actual Rust potential adjustment: 2026-11-14

`Rust.AssignmentAdjustmentLoop.adjust_potentials_spec` proves terminating,
successful execution of the entire generated adjustment loop. Exact vector
frames specify every row, column and slack slot, including untouched slots
and absent slacks. Injectivity of the actually used column pointers proves
each selected row is adjusted once. Premises are concrete representation,
injectivity and signed arithmetic bounds; no output correctness certificate
is supplied.

`Rust.AssignmentAdjustmentFeasibility` identifies the returned real potentials
with the independent cut update, proves feasibility and preservation of tight
edges, and proves that an edge attaining the cut slack becomes tight.
`Rust.AssignmentAdjustmentProgress.selected_cardinality` derives the cut's
one-extra-row property from actual used pointers and the reserved column zero.
`complete_dual_progress` and `complete_reserved_column` show that the actual
dual objective increases by the adjustment while reserved column slot zero
decreases by the same amount.

The full library compiles with these maintained modules. Establishing the
cut, pointer and numeric premises from the alternating-tree driver remains
open, as do path augmentation, reconstruction, entry-point correctness and
complexity refinement. No claim of a complete verified Hungarian solver is
made by this increment.

## Actual Rust potential-adjustment branches: 2026-11-14

`Rust.AssignmentAdjustment` proves all four generated adjustment branches.
`body_used_spec` verifies exact checked row addition and column subtraction
with the correct two array writes and unchanged slacks. The two unused-column
lemmas verify absent slacks remain absent and finite slacks lose the exact
adjustment. `body_done_spec` verifies the completion result. Premises are
input representation/index bounds and explicit signed arithmetic ranges.

Checked addition and subtraction now share `Rust.AssignmentArithmetic`; the
existing column-scan subtraction declaration remains a compatible proved
wrapper. The pinned signed-alias bodies are imported only in this arithmetic
module to bridge its public specifications, without dependency modifications.
The full library builds (3,563 jobs). Combining these branches with injective
matching rows into the full adjustment invariant, then deriving driver-level
feasibility, tightness and arithmetic safety, remains open.

## Complete actual Rust column scan: 2026-11-14

`Rust.AssignmentScanInvariant.scan_columns_spec` proves successful terminating
execution of the complete generated Rust scan, not just its individual
branches. The invariant tracks every processed/unprocessed slack and
predecessor slot and identifies minimum selection with Mathlib's stable finite
argmin. `scan_columns_minimum_spec` proves the returned column is positive,
unused, inside the matrix dimension, globally minimal over every unused
column's independent relaxed weight, and physically holds the returned minimum
in the updated slack table. The exact table-prefix identities are retained.

Premises describe finite vector/index representation, an available unused
column, and explicit range bounds on the two reduced-cost subtractions. They
supply no optimum or algorithm-correctness certificate. Deriving those numeric
bounds and availability from the full Hungarian state remains open, alongside
the adjust/augment phases and entry-point theorem. The full library builds
(3,561 jobs).

## Actual Rust column-scan branches: 2026-11-14

`Rust.AssignmentColumnScan.body_unused_spec` now proves the complete active
branch of the generated scan: safe index subtraction and reads, exact integer
widening and reduced-cost subtraction, correct slack/predecessor relaxation,
minimum selection and cursor advance. Its premises are finite representation
bounds and explicit intermediate `i128` range inequalities; these still need
to be derived for the complete Hungarian driver. `body_used_spec` and
`body_done_spec` cover the remaining two branches. The actual factored Rust
`select_delta` operation is proved to preserve the earlier column on ties and
realize the independent minimum (`select_delta_correct`, `chooseDelta_value`).

All three Rust oracle/certificate tests pass after the source refactoring,
pinned regeneration compares exactly, and the full library builds (3,560
jobs). These branch proofs are prerequisites for the full scan loop invariant;
that invariant, the outer Hungarian phases and entry-point total correctness
remain open.

## Actual Rust slack relaxation: 2026-11-14

The Rust column scan now calls a factored `relax_column` helper.
`Rust.AssignmentColumnScan.relax_column_spec` proves safe execution, exact
minimum selection, the resulting slack table, and predecessor changes exactly
on strict improvement. `relax_column_minimum_spec` connects its returned
`i128` value to the independent `WithTop ℤ` minimum, including absent slacks
and ties. Source-body lemmas also verify skipped used columns and scan
completion with a present minimum. A checked-subtraction lemma discharges
its success case under explicit integer range bounds.

All three independent Rust oracle/certificate tests still pass; pinned actual
source regeneration compares exactly. The full Lean library builds (3,560
jobs). The complete column-scan invariant and the subsequent potential-update
and augmenting-path loops remain open; this increment does not prove the
Hungarian entry point correct.

## Independent Hungarian cut adjustment and numeric bound: 2026-11-14

`Shared.AssignmentPotentials` proves `adjust_feasible`, preservation of tight
matching edges whose endpoints move together, and creation of a tight edge
attaining the cut slack. `exists_cut_adjustment` proves an attained nonnegative
step exists for every nonempty selected-row cut with a remaining column.
`adjust_dualValue_one` proves that a cut with one extra row raises the dual
objective by exactly its adjustment. `total_increment_bound` bounds cumulative
increments by `2*n*C` from dual feasibility, original cost bounds and the
accounting identity. These are ordered-ring matrix statements, independent
of the Rust program; deriving their premises from actual scan/adjust/augment
loops and discharging final machine-arithmetic bounds remain open. The full
library builds (3,559 jobs).

## Actual Rust feasible initial potentials: 2026-11-14

`Rust.AssignmentPotentialInitialization.initial_potentials_spec` proves the
actual generated Rust vector initializer safely terminates with exact row
minima in all real slots and zero in the reserved slot. Its prefix invariant
preserves previous writes and excludes the error branch on nonempty rows.
`initial_potentials_feasible_spec` proves that a represented square input and
representable `n+1` extent suffice to obtain a dual-feasible row vector with
zero column potentials, using the independent `Assignment.Feasible` matrix
contract. It derives row nonemptiness from square shape, and covers the empty
matrix. Integer widening, scalar increments, vector size checks and indexing
are discharged for the actual initializer. The full library builds (3,558
jobs). Subsequent scan/adjust/augment invariants, complete assignment entry
point correctness, total arithmetic bounds and runtime remain open.

## Actual Rust row-minimum scan: 2026-11-14

The integer Hungarian core now initializes each row potential from its row
minimum, with zero column potentials, so its intended starting dual state is
feasible even for negative costs. Input-shape checking and the augmentation
driver are separate functions to keep the pinned extractor's control flow
supported. The three independent permutation/dual-certificate Rust tests still
pass, and the regenerated actual semantics compile and compare reproducibly.

`Rust.AssignmentRowMinimum.minimum_row_spec` proves safe termination and exact
equality with Mathlib's finite minimum of the row's integer values.
`minimum_row_nonempty_spec` additionally proves that nonempty input returns an
actual row entry whose value is no greater than every row cost. The proof uses
a decreasing loop measure and exact prefix-minimum invariant, including the
empty-row result. The full library builds (3,557 jobs). Feasibility of the
complete initialized vector and the subsequent Hungarian phases remain open.

## Exact integer assignment core and initialization: 2026-11-14

The signed partial-matching/dummy-assignment reduction now works over ordered
commutative rings, including exact integers. `Shared.AssignmentDuality` proves
weak duality, exact cost under tightness and `tight_assignment_decodes`: feasible
dual potentials plus a tight permutation produce a globally optimal compatible
partial matching. `WeightedMatching.maximum_of_finiteWeights` proves that
removing bottom-valued edges before finite assignment preserves optimality for
the graph recurrences' `WithBot` objective. These are independent specifications,
not definitions of the Hungarian algorithm's result.

The new `rust/crates/verified_assignment_core` implements square signed-`i64`
Hungarian assignment with checked `i128` potential/total arithmetic and explicit
shape/arithmetic errors. Its three Rust tests pass: 320 signed matrices through
dimension seven agree with independent permutation enumeration; empty, ragged,
extreme-cost and tie cases also check bijectivity, dual feasibility and selected
edge tightness. The actual source exports through the pinned Charon/Aeneas
pipeline; regeneration comparison and generated Lean compilation pass.
`Rust.AssignmentInitialization` proves terminating, safe execution and exact
contents of all four actual initialization loops, via a common decreasing-rank
push-loop proof. The full library builds (3,556 jobs).

The Hungarian phase invariants, numeric bounds, full Rust entry-point optimum
and total correctness, partial-matching adapter and cost refinement remain open.
The floating graph API has not been replaced. CI includes the new core's tests;
its earlier remote run is now inspected; see the validated stopping checkpoint above.

## Executable 2016 and unrooted baselines: 2026-11-14

`Droschinsky2016.RootedDP.solve_correct` proves every entry of the executable
2016 descendant table equals the independent connected-isomorphism optimum.
`unrootedOptimum_correct` fixes one left orientation and tries all right roots,
then proves equality with the unrestricted nonempty optimum using Lemma 2.
`Droschinsky2018.RootedDP.unrootedOptimum_correct` similarly proves a full
all-root-pairs baseline for topological embeddings. These endpoints take only
finite vertex-list coverage and exact oriented child-list representation
hypotheses, over the shared real/integer scoring model.

Both evaluators now use `Shared.FiniteTable.rounds`: each round materializes
its table, with a general rank-based correctness proof and exact table-length
theorem. The actual tree ranks supply the bound. The 2018 entry points retain
their previous correctness statements after this refactoring.

The full library builds (3,552 jobs), and all nine kernel-evaluated examples
in `Tests/RootedDynamicProgram.lean` pass. The added cases distinguish a
connected isomorphism from a skipped-middle embedding, preserve a direct edge
reward, retain a negative singleton, and exercise both unrooted entry points.
These remain score-only references using linear table lookup, repeated rounds
and exhaustive matching. Returned index witnesses, accepted-representation
validation, actual Rust graph refinement, optimized paper schedules/matching
and their time/space bounds remain outstanding.

## Executable rooted 2018 evaluator: 2026-11-14

`Droschinsky2018.RootedDP.solve_correct` proves that the executable finite
association table contains both independent mapped/skipped witness optima.
`rootedOptimum_correct` proves the returned rooted score equals the source
nonempty optimum. Inputs supply complete finite vertex lists and child lists
representing the actual oriented tree edges; no optimum, acyclicity or
evaluation-order certificate is supplied. Fuel is computed as the two input
list lengths; canonical-path ranks prove that this suffices.

The evaluator supports exact integer arithmetic as well as the abstract real
model, and handles signed/bottom weights and finite/infinite penalties. The
matching proof now needs enumeration only of allowed pairs, so each update
enumerates its child product. Four compiled kernel-evaluated regressions
(`lake env lean Tests/RootedDynamicProgram.lean`) cover the scaled 1-edge/2-edge
discriminator (7), infinite penalty (4), negative singleton (-4), and forbidden
singleton (bottom). `lake build` succeeds (3,549 jobs).

This is a score-table reference with repeated synchronous rounds, linear
table lookup and exhaustive matching. Returned input-index witnesses,
representation validation, actual Rust graph refinement, optimized matching
and published time/space bounds remain outstanding.

## Shared real and integer scoring: 2026-11-14

The 2016 and 2018 specifications, witness score identities, finite optima,
rooted recurrences and overall optimum identities are now generic over an
ordered commutative ring `K`. `Droschinsky2016.Scoring V W K` retains explicit
negative infinity through `WithBot K`; 2018 retains infinite penalties through
`WithTop K`. Instantiating `K = ℝ` recovers the paper statements, while
`K = ℤ` gives the same contracts for exact integer computation. No float-to-real
identification is assumed. The full Lean library compiles after this change.
Executable score evaluators are described above. Checked machine arithmetic,
efficient matching and the published optimized running times remain outstanding.

## Fixed-orientation 2016 recurrence: 2026-11-14

`Droschinsky2016.Oriented.rooted_matching_recurrence` extends the compiled
whole-tree equation to every descendant pair in fixed ambient orientations.
Each selected neighbor is proved to be an actual oriented child; branch
restrictions retain the original roots. `familyOfMatching_rooted` and
`familyOfMatching_score` construct a feasible parent witness with exactly
the matching objective for every compatible matching. This supplies the
recurrence needed by recursive evaluation without silently rerooting input
subproblems. The full library builds (3,550 jobs); executable 2016 evaluation
and optimized matching/cost remain outstanding.

## Survivor enumeration completed before implementation reprioritization: 2026-11-14

`Shared/AssignmentSurvivingIndices` proves the increasing filtered original-index
list equals Mathlib's canonical `Fin.succAbove` enumeration.
`Rust/SparseDeletionVertices.surviving_vertices_spec` verifies the actual Rust
loop returns precisely that filtered list for every represented extent and
removed index. The deletion caller's remaining projection/refinement work is
open. Substantial further proof development is deferred under the updated
software-first development sequence; complete verification remains a final
verified-release requirement.

The source-only portable rebuild at `e272d36` now also passes all 199 tests on
glibc 2.28 and each CPython 3.10–3.14, with strict Linux/ABI auditing. This
updates the packaging evidence for the rooted graph APIs without changing
any mathematical, source-refinement or complexity assurance claim.
