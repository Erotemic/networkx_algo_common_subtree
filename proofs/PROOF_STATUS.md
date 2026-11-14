# Common-subtree proof status

## Accepted development: 2026-11-14

`cd proofs && lake build` succeeds under Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and Aeneas
`5a392f4b80a4d0d05abc240eb2a7fa70622a9a35`. This is an executed VM build,
not a maintainer-reported build. All maintained modules are imported by
`SubtreeProofs.lean`. Reproduction commands, pins, translation boundaries,
and bind-mount instructions are in [VERIFICATION.md](VERIFICATION.md).

The opt-in `BaselineAudit.lean` endpoint review established the initial
allowed set `propext`, `Classical.choice`, `Quot.sound`; no endpoint adds a
dependency outside that set. Raw output was captured during validation.
Routine development checks are targeted compilation, not repeated audits.

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
The distinct ordered-isomorphism contract, memoized cost model, index mapping
witnesses, actual Rust solver refinement and integration remain open.

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

## Executed independent evidence

- All 197 rooted ordered trees through six edges agree between independently
  enumerated tree contractions and matched-pair deletions.
- Lemma 8's numerical recurrence agrees with operational optima on 19,503
  unordered pairs from those trees. It disagrees with the literal printed
  objective on 7,554 pairs. This is finite evidence, not a general DP proof.
- The Python test suite passes 52 tests, with two extension tests skipped.
- The graph-only Rust crate passes 27 tests, including an exhaustive
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
| Translated Rust ordered reference solver | Proved for structural tree witnesses and u32 input bounds; memoized optimization, input-index witness maps and API conversion still open |
| Hungarian/assignment reduction and actual Rust matching correctness | Open; finite exhaustive matching is proved |
| 2016/2018 graph/path Lean specifications and DP/optimization proofs | Open |
| Verified Python adapters and qualified performance evidence | Open |

The overall program remains active. These results do not complete the paper
formalizations, published optimized algorithms, or end-to-end Rust verification.
