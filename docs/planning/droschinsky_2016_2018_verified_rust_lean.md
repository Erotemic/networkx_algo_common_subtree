# Droschinsky, Kriege, Mutzel (2016 and 2018): verified Rust and Lean plan

Status: independent graph/path specifications, finite optima and rooted recurrences proved; executable Lean DP baselines and actual Rust exact assignment/partial-matching public APIs proved; Rust graph refinement and paper optimizations open
Updated: 2026-11-14
Program charter: [Verified common-subtree research program](verified_common_subtree_research_program.md)

## Current software-first implementation milestone: 2026-11-14

Both graph families are now public NetworkX/PyO3 APIs, with optional labels,
signed scalar/callback weights, empty/nonempty objectives, original-node/path
witnesses and independent exhaustive references/rescorers. Exact source-proved
integer assignment/partial matching are also public Python APIs. The installed
Release wheel passes all 172 tests with compiled backends required. Python
conversion and f64 graph DPs remain tested, not source proved.

Measured optimization removes padded dummy matching matrices and roots the
2016 left input once. The latter yields 125x on 32-vertex stars and 3.63–6.04x
on ResNet-sized installed APIs over the preceding wheel. Reproducible API,
raw PyO3 and native Rust evidence is in the capability matrix and benchmark
reports. Dense all-right-deletion matching reuse is now integrated into 2016;
both families store reconstruction choices instead of full per-state mappings.
Independent deletion and graph oracles pass. The 2018 fixed-left mapped/skipped
schedule and skipped-highest path join are implemented and independently
tested. Constant-time view/edge lookup and complete production complexity/
refinement remain implementation and proof tasks. Substantial formal work below is
deferred until software coverage/correctness/performance are established;
existing proofs are preserved, and full verification remains a final-release
blocker.











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
its first remote run remains pending.

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

## Overall optima and rooted order accepted: 2026-11-14

The independent rooted 2018 optimum equals the maximum mapped-state entry.
Trying all ambient root pairs gives a correct unrooted baseline. The rooted
recurrence dependency order is derived from actual finite tree depths.
The optimized unrooted schedule, executable evaluation, matching implementation,
Rust refinement and cost theorems remain open.

## Full two-state recurrence accepted: 2026-11-14

`Droschinsky2018.mapped_recurrence` and `skipped_recurrence_two_state` now
prove both halves of Lemma 5 against independent concrete witness maxima.
The proof includes exact source correspondence, pointed witness construction,
matching assembly, arbitrary common-tree decomposition and complete vertex/path
score identities. Signed and negative-infinity weights and infinite penalties
are preserved. The matcher is a certified exhaustive oracle; executable DP
evaluation, the optimized matching algorithms, cost bounds and actual graph
Rust refinement remain open.

## Skipped-root recurrence accepted: 2026-11-14

`Droschinsky2018.skipped_recurrence_two_state` proves the diamond half of
Lemma 5 against independently optimized finite boundary witnesses. The common
top pair, fixed input orientations and boundary path penalties are explicit.
Both child-descent directions and exact one-penalty score changes compile,
including empty child families and infinite penalties. Mapped and skipped
maxima partition the boundary objective exactly. The mapped-root matching
half, executable evaluation, optimization and Rust refinement remain open.

## Fixed-root source contract accepted: 2026-11-14

The 2018 rooted and root-to-root feasible families now have separate exact
source equivalences for supplied ambient roots, proved in `Droschinsky2018.Rooted`.
Rooted admissibility requires a common selected top pair in both orientations;
root-to-root additionally maps the two input roots. Independent rooted score
attainment is proved. Mapped/skipped boundary states and the two-state recurrence
are the next mathematical obligations; graph Rust refinement remains open.

## Source correspondence accepted: 2026-11-14

`Droschinsky2018.valid_iff_source_embeddings` now proves the exact unrooted
witness correspondence with Definition 1's two local rooted clauses. The
source clauses imply global path disjointness and mapped-vertex avoidance;
finite skeleton witnesses yield explicit common trees and root-to-root source
embeddings at corresponding chosen roots. Abstract-tree and finite-pair scores
agree exactly. Fixed ambient-root admissibility, the two-state recurrence,
optimized algorithms and Rust refinement remain open.

## Topological witness direction accepted: 2026-11-14

`Droschinsky2018.Valid.rooted_realizations` now constructs an explicit common
tree and two injective embeddings satisfying both clauses of Definition 1,
with the root-to-root property at corresponding chosen roots. Their pair
relation is exactly the independent skeleton witness. Simple abstract paths
lift to simple target paths and preserve/reflect ancestry. Fixed ambient-root
restrictions, converse source correspondence, score bridge and the two-state
recurrence remain open; no graph Rust refinement is claimed.

## Rooted matching recurrence accepted: 2026-11-14

`Droschinsky2016.rooted_matching_recurrence` proves Eq. (1) against the
independent optimum, with valid witness decomposition and converse assembly,
exact vertex/edge score identities and certified optimal child matching.
It preserves signed and negative-infinity weights. The matcher is an exhaustive
oracle and continuation values are independent finite optima; efficient
recursive evaluation, Hungarian refinement, Rust verification and runtime
claims are still open.

## Fixed-root reduction accepted: 2026-11-14

`Droschinsky2016.fixedRootValue_eq_unrootedValue` proves 2016 Lemma 2
against the independent graph and score specification. Connected selected
subtrees have a unique top vertex in any fixed left orientation; this supplies
a rooted representative without changing the witness or score. Ancestry uses
canonical graph paths, with path closure and injective-map invariance proved.
The child-matching recurrence, algorithm refinement and complexity are open.

## Matching reduction accepted: 2026-11-14

`WeightedMatching.AssignmentReduction.minimum_assignment_decodes` now proves
an exact dummy-assignment reduction for optional partial matchings with
forbidden pairs and signed real weights, without a magnitude bound. The Rust
reference uses the same zero-profit construction in place of numeric sentinels,
retains tiny positive selected weights, and rejects nonfinite inputs/arithmetic.
All 35 graph-crate tests pass. Hungarian-loop correctness, floating-point
refinement, efficient matching bounds and the graph recurrences remain open.

## Graph foundations accepted: 2026-11-14

`Droschinsky2016.Specification` defines nonempty connected partial-bijection
witnesses, unordered-edge scores over real weights with negative infinity,
and proves an attained optimum for every finite-tree pair. `Witness` builds
a genuine induced-graph isomorphism and proves both selected objects are trees.
`Droschinsky2018.Specification` defines unrooted skeletons with disjoint path
interiors, exact Definition 4 path contributions, finite optima and general
penalty monotonicity. Rooted ancestry, source-embedding correspondence, paper
DP proofs and faster matching work remain open.

Rust/Python now expose explicit nonempty reference APIs retaining negative
optima and returning `None` for incompatible inputs. Existing APIs retain their
explicit empty-allowed convention. Rust passes 30 graph tests; Python passes
55 tests with two extension skips. These are reference implementation tests,
not refinements of the graph Rust code to the new Lean specification.

## Accepted increment: 2026-11-14

The Python reference and Rust two-state DP now implement Definition 4's
path score, including longer paths with incompatible edge labels. Both 1.75
discriminators pass. An independent Rust partial-injection oracle validates
small-tree optima and returned witnesses, including negative vertex weights
and edge rewards. The Python oracle rejects omitted branch points.
`WeightedMatching.solveMatrix_correct` proves an executable exhaustive
integer-weight partial-matching solver; Hungarian refinement and paper DP
proofs remain open. The graph-only Rust suite passes 27 tests.

See [current proof evidence](../../proofs/PROOF_STATUS.md) and
[reproduction instructions](../../proofs/VERIFICATION.md). Historical baseline
and pending-build descriptions below are superseded by this increment.

## 1. Scope: two papers, two objectives

These papers are independent of the Lozano-Valiente ordered-tree proof, though
some definitions and formal proof infrastructure can be shared. Do not conflate
subtree **isomorphism** (edge-to-edge adjacency preservation) with a topological
**embedding** (an abstract edge can be realized by a longer input-tree path).

| Reference | Mathematical objective | Intended proof targets |
| --- | --- | --- |
| Droschinsky, Kriege, Mutzel, *Faster Algorithms for the Maximum Common Subtree Isomorphism Problem* (2016), [arXiv:1602.07210](https://arxiv.org/abs/1602.07210) | Maximum-weight connected common subtree isomorphism for unordered, potentially unrooted trees | Correct witnesses, rooted/unrooted DP, child matching, specialized matching speedups and claimed `O(n^2 Delta)` bound |
| Droschinsky, Kriege, Mutzel, *Largest Weight Common Subtree Embeddings with Distance Penalties* (2018), [arXiv:1805.00821](https://arxiv.org/abs/1805.00821) | Maximum-weight common topological embeddings with skipped internal vertices and path penalties | Correct path/skeleton semantics, full scoring rule, rooted/unrooted recurrence, paper optimization and qualified complexity |

The goal is a **faithful mathematical formalization of both papers** and a
proof of a Rust implementation against each mathematical problem. A Rust
solver that computes correct answers using a slower reference recurrence
would satisfy part of that goal but **not** the full paper-level optimization
and complexity target.

## 2. Actual repository baseline

The supplied `af0bbdb` repository snapshot contains:

- `rust/crates/common_subtree_algorithms/src/matching.rs`: a weighted
  Hungarian-style solver used for partially matched child sets.
- `rust/crates/common_subtree_algorithms/src/tree.rs`: connected common subtree
  isomorphism DP and an **experimental** path-embedding DP.
- `rust/crates/common_subtree_algorithms/tests/matching_reference_tests.rs`:
  deterministic matching/independent brute-force tests.
- `rust/crates/common_subtree_algorithms/tests/tree_isomorphism_reference_tests.rs`:
  small enumerated tree-pair and witness tests.
- `rust/crates/common_subtree_algorithms/tests/embedding_reference_tests.rs`:
  a small set of skipped-path and witness tests, **not a paper-correct oracle**.
- `networkx_algo_common_subtree/common_subtree_reference.py`: separate slow
  pure-Python implementation with exhaustive graph enumeration in some paths,
  but sharing the 2018 paper-semantic problem described below.
- `dev/common_subtree_algorithms_notes.md`, `dev/notes/notes.txt`,
  `docs/source/common_subtree_correctness.rst`, and ResNet-like tree benchmarks.

The Droschinsky crate is **not integrated into the Python extension**. The
ordered-tree PyO3 backend in `rust/src/lib.rs` is a different code path.
Retain this separation until mathematical contracts and adapters are explicit.

### Historical test evidence (do not claim a new passing run)

The previous audit found the 2016 source tests comparing 1,764 pairs of small
labeled trees plus 64 additional examples, identity cases through five
vertices, and 1,600 deterministic small matching matrices. The 2018 test file
contained seven focused tests. An earlier Python test run reported 25 passing
reference/property/correctness tests. Cargo could not be executed in that
audit environment, and no dedicated CI invocation of the Droschinsky crate's
`cargo test` had been established. These are coverage observations, **not**
proof of either published algorithm.

## 3. The known 2018 mismatch is a release blocker

The earlier paper-versus-source audit identified a substantive disagreement
between the published 2018 objective and the Python/Rust scoring convention:

- A mapped skeleton edge whose corresponding paths both have length **one**
  may contribute the direct compatible edge-pair weight.
- If **either** path has length greater than one, the paper's formulation
  uses the negative distance penalty for its skipped internal vertices,
  **without** adding a direct first-edge match reward.
- The current Python and Rust implementations instead award the first-edge
  reward on longer paths, and the reference can reject permitted longer-path
  mappings when those first-edge labels are incompatible.

Record these fixed discrimination cases as independent mathematical examples.
The weights below are the controlled values in the previous audit, not the
result of a new run:

| Case | Left and right inputs | Published score | Current Python result in audit |
| --- | --- | --- | --- |
| Skipped path, incompatible direct edge labels | Two endpoint vertices on the left connected by one edge labeled `5`; right side is a three-vertex path with both edge labels `9`; endpoints compatible with vertex weights 1 each, middle label different; skip penalty 0.25 | `1+1-0.25 = 1.75` | `1.0` (only one mapped vertex; rejects the valid longer-path mapping) |
| Skipped path, matching first-edge labels | Same trees and weights but right edge labels changed to `5` | `1.75` | `2.75` (adds an edge match reward that the paper does not award) |

The current witness rescoring code shares the implementation's convention;
comparing Rust against that Python oracle cannot detect the error. Before
changing the DP, write a paper-specific scorer with **no calls to** the
production scorer, and a brute-force path/skeleton enumerator. Fix both
feasibility and scoring. If a useful alternative first-edge-reward objective
is deliberately retained, give it a separate API name and a distinct spec;
it cannot stand in for the 2018 theorem.

**Gate D18-S:** both cases return the paper-correct optimum and a valid
independently rescored mapping in the exact small-tree oracle and the Rust
reference. Add further examples to confirm the general rule, not merely these
two fixed outcomes.

Also audit the older `docs/source/common_subtree_correctness.rst` wording:
it currently describes an endpoint-edge contribution on skipped paths. Align
that documentation with the verified paper rule when the correction is made.

## 4. Independent mathematics to specify

### Common finite graph/tree foundation

Use a finite vertex type, a loop-free symmetric adjacency relation, a
connected/acyclic proof, and **unique simple paths** in a tree. Fix labeling,
edge identity, root orientation, node/edge compatibility, and score domains.
Weights may need signed values and forbidden pairs; distinguish incompatible
(`none`) from compatible with weight zero. Decide explicitly whether the empty
common object is permitted and what negative score should return; the paper
may require a nonempty connected common subtree even when its score is negative.
Do not silently clamp all values to zero without a stated convention.

Useful general proof infrastructure includes:

- finite subsets and their induced connectedness;
- partial injections/bijections and a concrete mapping witness;
- isomorphism of the chosen connected subtrees;
- unique paths, interior vertices and path lengths;
- maximum over a finite feasible witness set, with a proved existence theorem;
- independent score evaluation and equality of witness score to reported score.

Do not choose Aeneas-generated Rust graph types as the specification's types.
They belong to the refinement layer. Keep generic infrastructure only where
there is real reuse across both papers.

### 2016: common subtree isomorphism

An abstract witness should specify nonempty connected vertex subsets in both
input trees and a bijection preserving adjacency in both directions. Compatible
mapped vertices and edges contribute their explicit weights. Score it by
summing each mapped vertex and abstract edge **exactly once**. Prove that
candidate feasibility and scoring are decidable/finite where required.

Rooted states can orient an unrooted tree at a selected mapped pair and a
parent-edge exclusion. Child continuation choices form independent neighbor
branches, so optimal selection is a **maximum-weight partial bipartite
matching**. The matching proof must cover forbidden choices and unmatched
children. Establish rooted-to-unrooted coverage rather than assuming a fixed
input root always contains the optimum.

### 2018: topological embedding with distance penalties

Model an abstract connected skeleton tree with two injective maps into
selected vertices of the inputs. Every skeleton edge has a **unique path**
between its mapped endpoints in each input tree. Consecutive selected vertices
and exclusion of other selected vertices along that path determine the
skeleton. Prove no prohibited path sharing/branch overlap; pin the paper's
exact admissibility constraints before choosing the final Lean encoding.

Define node weights and, per abstract skeleton edge, the paper's direct-edge
contribution *only when both realizations are single edges*. Otherwise define
the precise penalty from intermediate vertices/path length(s), without a
first-edge reward. Reconcile how the paper handles differing penalties per
input, incompatible edge pairs, negative weights and nonempty solutions.

Obligations: a witness is structurally feasible; all path interiors are
accounted for once; every feasible embedded solution is represented by the
independent skeleton mapping; scoring agrees with the paper; the optimum is
attained on finite trees. Use the paper's actual definition rather than the
prototype's `skip_vertex_penalty` parameter as the starting point.

## 5. Matching as a shared, independently proved foundation

Define a finite partial matching as a set of compatible left/right pairs
with no repeated endpoint. Its weight is the sum of selected edge weights,
with unmatched endpoints permitted when allowed. The optimum is the maximum
of these scores over all valid partial matchings.

1. Prove the basic match-validity, score and finite-optimum lemmas.
2. Implement a deliberately slow exhaustive matching oracle; test matrices
   with empty sides, ties, negative/zero scores, rectangular shape, forbidden
   entries, partial matchings, and high magnitude values.
3. Prove a mathematical Hungarian/assignment reduction when appropriate:
   dummy rows/columns, transformation of maximization to minimization,
   forbidden edges, and preservation of the chosen optimum. Avoid assuming
   complete equal-sized assignment is the same problem.
4. Check [CLRS-Lean](https://github.com/TankTechnology/CLRS-Lean) at an exact
   compatible revision before reusing its existing Hungarian development.
   A mathematical assignment-existence/optimality result is not automatically
   a theorem about our Rust `matching.rs`.
5. Verify the actual Aeneas-translated Rust matching routine against the
   finite-matching specification, including index bounds and arithmetic
   contracts. If translation is infeasible, provide a smaller verified
   matching core and compare/replace the existing solver on evidence.

This work is worth starting alongside early Lozano-Valiente mathematics. It
is essential for 2016 and likely useful for 2018, while tree-order conventions
should remain paper-specific.

## 6. 2016 paper proof and optimization sequence

**M16-A: mathematical recurrence.** Prove that deleting the mapped roots
separates usable branches and that an arbitrary valid rooted witness induces
a partial matching of child branches. Conversely, assemble any compatible
matching of valid continuations into a valid rooted witness. Derive the
recurrence's optimality from these two directions, not by defining optimum
as its recurrence. Include witness reconstruction and all-root-pairs coverage.

**M16-B: reference implementation.** Prove an executable Lean/reference DP
matches that optimum. Audit Rust tree/edge label and scoring API behavior,
including error/empty/negative cases. Expand Rust versus independent
brute-force testing and require a passing `cargo test` in CI.

**M16-C: faster algorithm.** Work through the paper's shared/reused matching
instances, prove their relation and the optimized update rules, and establish
the published `O(|G|*|H|*(min(DeltaG,DeltaH)+log(max(DeltaG,DeltaH))))` operation bound under explicit arithmetic and
container assumptions. The existing repeated Hungarian approach cannot be
claimed to meet this theorem merely because the recurrence is correct.

**M16-D: verified Rust.** Translate a proof-friendly implementation with
Charon/Aeneas; prove the entry point returns a feasible globally optimal
mapping and score for accepted inputs. Then verify/refine optimized changes
rather than discarding performance evidence. Provide reproducible tool pins,
regeneration, theorem dependency review, and benchmark comparisons.

## 7. 2018 paper proof and optimization sequence

**E18-A: authoritative oracle.** Write the path/skeleton feasibility and
score specification independently of Rust and Python source. Make the two
counterexamples in section 3 pass; add exhaustive small-tree tests covering
path lengths, labels and penalties. Do this before restructuring the DP.

**E18-B: branch/path recurrence.** Establish branch independence when
skipped vertices are allowed, recurrence soundness, coverage of every feasible
skeleton, and proper penalty accounting. Handle rooted and unrooted cases as
specified by the paper, with explicit witness paths and all score components.

**E18-C: optimized paper algorithm.** Identify exact optimized constructions,
state families and claimed bounds from a pinned paper version; prove the
specific improvements and count work of an actual algorithm. Record a theorem
crosswalk, including hypotheses and any changes needed to the printed claims.
Do not invent a bound by analogy with the 2016 algorithm.

**E18-D: verified Rust.** Replace or distinguish the current incorrect
prototype, build an Aeneas-friendly Rust core, and prove a refinement from
generated Lean to the independent paper optimum and an explicit witness.
Integrate into Python only after conformance and performance gates are met.

## 8. Research-library candidates

- **Mathlib:** finite graphs, trees, unique paths, `Finset`, equivalences,
  injections, finite maxima, recursion, cost/asymptotic syntax.
- **TauCeti:** `Combinatorics.SimpleGraph.Paths` for endpoint/interior path
  decompositions; `Combinatorics.Graph.Matching.Basic` for matching validity.
  Inspect signatures and build compatibility before depending on them.
- **CLRS-Lean:** Hungarian algorithm mathematics, potentially reusable for
  the 2016 child-matching part after a proved partial-matching reduction.
- **Lean Std/Batteries:** executable data structures for implementation
  models; abstract theorem statements must remain representation-independent.
- **Charon/Aeneas:** real Rust extraction into Lean; evaluate supported
  numeric types, loops, indexing, collections and error handling early.

Do not force Mathlib and TauCeti pins to diverge just to use one small lemma.
A precise independent proof plus a prospective upstream PR may be better when
upstream compatibility is the limiting issue.

## 9. Work packages and acceptance gates

| ID | Work | Depends on | Acceptance |
| --- | --- | --- | --- |
| D0 | Pin source editions and create paper-to-Lean statement ledgers | none | Each paper's definitions, lemmas, theorems, assumptions and complexity claims inventoried |
| D1 | Independent finite-tree, path, mapping and score specification | D0 | Small checked examples, genuine finite feasible optima |
| D2 | Partial weighted matching spec, exhaustive oracle, reduction | D1 | Matching theorem plus independent negative/forbidden/unmatched tests |
| D3 | Fix 2018 paper scoring and feasibility oracle | D1 | Gate D18-S and exhaustive path cases |
| D4 | 2016 rooted/unrooted recurrence and witness proof | D2 | Executable mathematical DP equals independent optimum |
| D5 | 2016 optimized matching updates and operation bound | D4 | Verified paper-specific `O(|G|*|H|*(min(DeltaG,DeltaH)+log(max(DeltaG,DeltaH))))` assumptions and actual work |
| D6 | 2018 path/branch recurrence, witness and optimum | D3, D2 | Executable paper recurrence equals independent maximum |
| D7 | 2018 optimized method and complexity | D6 | Exact paper bound proved or documented correction |
| D8 | Aeneas translation/refinement for verified Rust matching and DP(s) | D2, D4/D6; translation spike parallel | Theorem about actual translated Rust entry point, generated Lean reproducible |
| D9 | CI, paper examples, independent differential tests, performance, Python integration | D4-D8 as relevant | Validated witness, measured scaling, correct dispatch and no hidden fallback masking |

**Priority:** stabilize 2016 reference tests/semantics and the shared matching
spec, while independently correcting the 2018 oracle. Formalize 2016 first;
2018 adds topological path bookkeeping and its current source cannot yet be
trusted as a paper-correct differential oracle. An Aeneas translation spike can
proceed in parallel with mathematical definitions.

## 10. Proposed module boundaries (create only when needed)

A useful conceptual arrangement is:

```text
proofs/SubtreeProofs/
  Shared/                 # finite-tree witnesses, paths, weighted partial matching
  Paper2004/              # existing ordered contraction and Dyck-word work
  Droschinsky2016/        # rooted branch DP, optimality, fast matching/cost
  Droschinsky2018/        # skeleton paths, penalty score, DP/cost
  Rust/                   # paper-specific Aeneas imports and refinement
rust/crates/
  common_subtree_algorithms/  # existing graph-only reference crate
  ...                     # verified core crate(s), if translation requires them
```

This is a separation of proof responsibilities, **not** a directive to create
placeholder modules or copy generic graph code everywhere. Shared proofs
should capture genuine agreement of semantics; paper-specific modules should
make disagreements visible. Keep exported definitions grep-friendly and named
for their domain.

## 11. Tests and production integration

- Make every Rust Cargo test target part of CI. Use a fresh, pinned Rust
  toolchain, record command and outputs, and never describe a source-inspected
  suite as a passing run.
- Exhaustively enumerate small connected subtrees and injective mappings,
  partial matchings and embedding skeletons. Compare optimal scores and
  independently evaluate the *returned witnesses*.
- Add property tests for renaming/vertex relabeling where score functions
  transform accordingly; input swapping when weight functions are symmetric;
  nonincreasing optimal score as nonnegative skip penalty rises; and
  adversarial branching/matching cases.
- Test integer overflow, invalid indices, nonfinite floating values if
  accepted, incompatible labels, ties, empty-versus-nonempty policies, and
  skipped paths with edge mismatches.
- Benchmark high-degree stars (repeated matching stress), chains, balanced
  and random trees, and existing ResNet-like module containment examples.
  Compare baseline Hungarian DP, optimized 2016/2018 solvers and any verified
  core with reproducible hardware/flags, time and memory profiles.
- Add Python/NetworkX adapters only once objectives, edge/vertex compatibility,
  witness shape and error policy are stable. Don't merge unordered weighted
  semantics into ordered balanced-sequence APIs implicitly.

## 12. Literature, provenance and scope boundaries

- Primary 2016 paper: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2016.33
- Primary 2018 paper: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2018.54
- Earlier repository materials: `dev/common_subtree_algorithms_notes.md`,
  `dev/notes/notes.txt`, `docs/source/common_subtree_correctness.rst`, and the
  Rust/Python source/tests described above.

The prior audit found notes saying that reference implementations were shared
by an author on 2025-03-12 and that parts were ported to Rust on 2026-05-12.
The notes did not themselves include private correspondence or source code.
Keep permission/provenance records for any nonpublic-source derivation, and
base the publicly claimed algorithm specification on the published papers.

The earlier C/Cython/PyO3 work on **ordered** balanced sequences is a useful
backend baseline for Lozano-Valiente; it is not evidence that the 2016 or 2018
unordered algorithms have already been fully implemented or verified.

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
