# Common-subtree proof status

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

## Outstanding obligations

| Target | State |
| --- | --- |
| Fresh-checkout local reproduction | Passed from `git archive 6dbf81e` on local disk with a fresh `.lake`; `lake exe cache get && lake build` fetched pinned dependencies and built 3,473 jobs |
| First remote CI run | Pending; workflow added |
| Pinned source statement ledgers for all three papers | Added `docs/planning/paper_statement_crosswalk.md`; open source results are explicit |
| Paper D/R/S and actual tree-parameter state bounds | Proved, including `states_closed` / `states_least` for Definition 4 |
| Lemma 8 recurrence optimum and tree witness | Proved; input-index reconstruction still open |
| LCBS/isomorphism's distinct ordered contract and optimum | Open |
| Computation-specific complexity | Memo operation and association-list comparison counts proved; full structural/dictionary cost and Theorem 3 runtime still open |
| Translated Rust ordered solvers | Reference and owned-memo entry points proved, including exact updated-cache refinement and state bound; efficient dictionary/bit cost, input-index witnesses and API conversion remain open |
| Hungarian/assignment reduction and actual Rust matching correctness | Exact signed-real dummy reduction proved; Hungarian loop, numeric refinement and complexity open |
| 2016/2018 graph/path specifications | Nonempty unrooted witnesses, real/negative-infinity scores, finite optima and 2016 induced-isomorphism bridge proved; 2016 fixed-root Lemma 2 proved; 2016 rooted matching Eq. (1) and 2018 unrooted source correspondence proved; fixed ambient-root states and both 2018 boundary recurrences proved; executable rooted 2018 score evaluator proved; optimized algorithms and actual Rust graph refinement open |
| Verified Python adapters and qualified performance evidence | Open |

The overall program remains active. These results do not complete the paper
formalizations, published optimized algorithms, or end-to-end Rust verification.











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
