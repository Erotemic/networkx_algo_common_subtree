# Lozano-Valiente (2004): fresh Lean formalization and verified Rust implementation

Status: LCBE and affinity-aware ordered-isomorphism mathematical optima proved; reference Rust and production integer witness components source proved; full optimized/weighted Rust correspondence and complexity remain open
Last revised: 2026-11-14
Paper: Antoni Lozano and Gabriel Valiente, *On the Maximum Common Embedded Subtree Problem for Ordered Trees* (2004)
Repository: `networkx_algo_common_subtree`
Program charter: [Verified common-subtree research program](verified_common_subtree_research_program.md)

## Original-identity affinity isomorphism extension: 2026-11-14

`Paper2004.AnnotatedIso` now specifies whole-subtree deletion independently as
an operational closure on annotated forests. Structural selection is proved
equivalent; parent edges, original preorder and identities are preserved.
Erasing annotations recovers the existing unlabelled isomorphism specification.
Fixed-parent and freely chosen parent-region policies remain distinct.

`AffinityDP.level_correct` and `AffinityDP.anywhere_correct` prove complete
witnessed optimality for original-node affinity scores over an ordered
commutative ring. Witnesses pair original identities, require positive affinity
at each retained pair and preserve endpoint uniqueness for unique input IDs.
Zero affinity forbids retention. This formalizes the project's intended
isomorphism/scoring extension; it is not an additional recurrence from the
original 2004 paper and does not change the LCBE containment audit.

The production integer arena has an independent projection to these witnesses.
Actual local construction preserves feasibility from head/tail invariants;
actual emission retains the same original-endpoint witness. Its safe output
size follows from the smaller original input once caller feasibility is proved.
Full optimized Rust DP/memo/state/score correspondence, conversion and runtime
remain open. IEEE-754 remains outside initial scope. All 3,739 main Lean jobs
and both example suites pass, including six new kernel-checked affinity cases.
Rust/Python are fixed; no benchmark or extraction run was repeated.

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
passes with the guided implementation. The linear bound counts witness calls,
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

## Verified Rust memoization: 2026-11-14

The actual owned-memo Rust entry point now has a compiled end-to-end optimum
and exact-score theorem (`Rust.MemoizedOrderedSolver.maximum_common_embedding_of_trees`).
Its returned cache equals the numeric memo model after erasing witnesses;
cache keys are unique and bounded by the proved D-product. Both Rust solvers
pass all 38,809 ordered pairs through six edges. The linked-list table has
linear scans and copied witnesses; efficient dictionary/representation cost,
input-index mappings, ordered isomorphism and Python integration remain open.
See [proof status](../../proofs/PROOF_STATUS.md) and
[shape benchmarks](../../dev/benchmarks/2026-11-14-ordered-memo.md).

## 2004 proof tranche accepted: 2026-11-14

The operational Lemma 8 recurrence now has a general constructive correctness
proof (`paperCommon_correct`, `paperCommon_tree_correct`), plus a separate
numeric recurrence theorem (`paperLcs_optimum`). Definition 4's least state
family, Lemmas 1--6, Fact 2, corrected actual-leaf bounds and Theorem 1 in
independent tree parameters compile. Theorem 2 is proved for operational
containment. Exact endpoints and all remaining obligations are in the
[paper statement crosswalk](paper_statement_crosswalk.md).

This closes the ordered LCBE mathematical optimum and state-bound chain.
Full implementation cost, input-index witness reconstruction, the distinct
ordered-isomorphism contract and Python integration remain open.
A fresh source-only checkout reproduced the previous full library build.

## Accepted increment: 2026-11-14

The complete existing library and new `ContractionOracle.lean` compile in
the VM. `mem_contractions_iff` proves the independent tree enumerator complete;
`maximumCommonContraction_correct` proves its returned tree globally optimal.
The printed-containment counterexample is compiled. W6 is now demonstrated:
pinned real Rust extraction, reproducible generated Lean and
`Rust.contractionBudget_refines_tree` all pass. W3-W5 and W7-W10 remain open;
this exhaustive baseline does not prove Lemma 8 or a polynomial-time solver.

See [current proof evidence](../../proofs/PROOF_STATUS.md) and
[reproduction instructions](../../proofs/VERIFICATION.md). Historical baseline
and pending-build descriptions below are superseded by this increment.

## 0. Present state and immediate milestone

The old `proofs` branch and v3-v6 proof sources are retired from active imports.
The restart **has already occurred**; do not run the earlier removal/reset
instructions again. Existing Rust/Python/Cython algorithms and Git history
remain intact. As of commit `b94593e`, the new Lean source and Lake project have
been committed.

The fresh Lake workspace requests Lean 4.35.0 and Mathlib `v4.35.0`.
The first drafted sources are:

- `proofs/SubtreeProofs/Paper2004/OrderedTree.lean`: finite rooted ordered
  trees, true leaf/edge counts, one-hole contexts and arbitrary-depth edge
  contractions, reflexive-transitive embedding and independent optimum.
- `proofs/SubtreeProofs/Paper2004/BalancedSequence.lean`: encoding into
  Mathlib `DyckWord` and a proposed semilength theorem.
- `proofs/PROOF_STATUS.md`: intended theorem-level evidence inventory.

**Observed build status:** the user reports that `cd proofs && lake build`
**now succeeds** after the constructor-elaboration correction. The initial
build failures (automatic `DecidableEq`, mutual syntax, the kernel-invalid
mutual contraction relation, arithmetic and `.node` elaboration) have been
resolved sufficiently for the current Lean sources to compile. This is a
reported local build result; a fresh-checkout reproducibility run, the exact
build log, and theorem-axiom audit have not yet been recorded. Prior Mathlib
module-system import warnings were nonfatal.

**Latest Lean build reported by maintainer:** the original ordered-tree
foundation, `EncodingEquivalence.lean` (including both round trips) and
`ContractionSoundness.lean` (including `embeds_encodeDyck`) now compile under
Lean 4.35.0 following the successive parser and constructor fixes. This
supersedes the earlier statement that these two modules were build-pending.

**New converse increment (pending local compilation):**
`ContractionCompleteness.lean` introduces forest decoding, proves decoding
respects concatenation and nesting, relates deletions in a `DyckContext` to
ordinary tree contractions, and states the two-way bridge
`embeds_iff_dyckEmbeds`. It is included as authored source, not yet reported as
accepted by Lean. The result concerns our explicit Dyck deletion relation;
agreement with the paper's exact balanced-containment convention still needs
independent review.

**Next action:** compile the new converse module and run `#print axioms` on
the two-way theorem. Then add an independent tiny-tree contraction oracle and
check the exact containment definition against the 2004 paper. Preserve the
passing baseline and lockfile, and add focused Lean CI. A passing build establishes Lean
acceptance of the current declarations; it does not establish the 2004
paper's contraction/sequence equivalence, recurrence, complexity claim, or any
Rust refinement.

Do not conflate the existing `ContractStep` implementation with proof of
agreement with the paper's exact root/edge contraction convention; that
correspondence is still a first-phase mathematical obligation.

## 1. Research goal and boundaries

Formalize the **original 2004 paper**, including its problem specification,
mathematical correspondence to balanced sequences, decomposition lemmas,
correctness of the dynamic program, constructive witnesses and the genuine
complexity argument. Then prove that an executable **Rust implementation**
translates through Charon/Aeneas and refines the independent Lean optimum.
Finally measure and integrate a competitive solver into the existing
NetworkX-facing API.

Verification is layered: the independently defined maximum, the paper
algorithm's recurrence and complexity, the Aeneas-translated Rust entry point,
and the Python integration are separate results. A proof of each is required
for a corresponding completion claim. Mathlib is the initial foundation;
TauCeti is optional pending exact theorem/dependency evidence. Neither the
old Lean experiments nor the existing Rust solver defines the problem.

The reset applies **only to old proof code**. Keep the optimized ordered Rust
baseline (`rust/src/lib.rs` with `Solver::emb`, `Solver::iso`, `decompose1`,
`decompose2`, memoization and PyO3 bindings), Python/Cython variants, tests,
benchmarks, relevant Git commits and history. No need to reimplement the
already working native algorithm before doing semantics; the future
proof-friendly Rust core will be compared against it. Do not merge the old
`proofs` branch or copy its declarations.

Targets:

1. Independent finite-tree embedding and optimization specifications.
2. Two-way tree contraction / Dyck-word containment equivalence and exact
   encoding/decoding round trips.
3. Real DP optimality (including witness soundness/completeness), not merely
   a recurrence defined to equal itself.
4. Paper definitions, Facts, Lemmas, Corollaries and Theorems crosswalk,
   including any necessary correction to a printed statement.
5. Complexity expressed as operations of an actual algorithm with finite
   decomposition-state bounds and explicit dictionary assumptions.
6. Verified translated Rust solver, including accepted-input safety and
   output witness, with reproducible generation and theorem dependencies.
7. Independent tests, measured scaling, and production integration.

Avoid proof-specific shims inside the mathematical specification, vague generic
helper names, one-off optimized Rust changes without semantic evidence, and
claims of verification based only on tests or authored uncompiled Lean.

## 2. Lessons from the retired proofs

These are hard requirements for the fresh development, not a plan to resurrect
old files:

- `Lozano-v6` used an encoded-containment relation as its notion of embedding;
  it therefore did not prove the missing edge-contraction correspondence.
- Its `lcsLen` recurrence was unfolded from the way `lcsLen` was defined;
  it did not prove equality with an independent maximum common embedding.
- Its runtime result was conditional on a cost formula and state hypotheses
  rather than operation counts derived from an executable algorithm.
- The printed `ell(nil)=1`, `ell(0 x 1 y)=ell(x)+ell(y)` recurrence yields
  `semilength+1`, **not actual tree leaves**; this matters for the claimed
  leaf-sensitive running time. The one-edge tree `01` has one leaf but the
  recurrence gives two. Resolve the correct combinatorial bound explicitly.

Retain historical examples only as evidence of what needs checking. Never
inherit their proof assumptions, theorem names or architecture.

## 3. Precisely define the first verified problem

Begin with finite, rooted, **ordered**, unlabeled trees. An embedding is obtained by contracting edges while preserving left-to-right child order, with the root convention established from the paper before proceeding. Measure optimality in **edges**, stating the corresponding node-count relation. Distinguish the one-vertex tree (zero edges) from an empty forest or invalid input. Precisely define valid trees and the domain of every public function.

The first theorem must have no dependence on NetworkX objects, labels, Python callbacks, optional affinity functions, weighted scores, unordered trees, or Droschinsky-style algorithms. Later extensions will have separate specifications and theorems. Retain the existing implementations as comparison targets only; behavioral agreement with them is not the definition of correctness.

Required independently defined objects:

- `OrderedTree`, forest, child order, size, depth, and **actual number of leaves**;
- contraction at any permitted edge/position, its reflexive-transitive closure, and the common-embedding relation;
- feasibility of a proposed answer, score, optimal value, and optimal witness;
- balanced-sequence grammar, sequence operations, length, encoding and decoding;
- sequence containment stated independently of the future DP;
- an executable exhaustive oracle for tiny trees based on contraction enumeration (not the paper's DP).

**Specification gate:** handwritten examples and exhaustive small-tree oracle outputs agree with the selected interpretation. Every edge/root/leaf convention is documented with at least one discriminating example. No production algorithm is imported by the specification.

## 4. Proof architecture and theorem obligations

Work in dependency order. Create modules only when their mathematical boundary is clear; prefer descriptive, grep-friendly theorem and function names over generic helpers that duplicate names elsewhere.

### A. Trees, encodings, and semantics

1. Define finite ordered rooted trees, forests and edge contractions in Lean without balanced sequences.
2. Define balanced sequences and their algebra, then prove encode/decode correspondence and structural invariants.
3. Define paper-style containment and an operational deletion relation independently. Prove both directions of their equivalence.
4. Prove **both directions** of the correspondence between sequence containment and the reflexive-transitive closure of tree contractions, including contractions inside nested children and splicing order.
5. Prove the stated relation between sequence semilength and the number of tree edges.

**Gate A:** `u` embeds into `t` under the independent tree relation if and only if `encode u` is contained in `encode t`; neither side is defined as the other.

### B. Decomposition combinatorics and the paper's bounds

1. Reconstruct the decomposition state set and auxiliary families (`D`, `R`, `S`) as mathematical finite sets; prove their recurrences and the paper's inclusion lemmas.
2. Inventory the paper's Definitions 1-5, Facts 1-2, Lemmas 1-8, Corollaries, and Theorems 1-3. Maintain one paper-to-Lean ledger identifying literal statements, clarified statements, and any required correction.
3. Derive cardinality bounds for decomposition states from the new definitions. Pay particular attention to `nil`, single-child trees, degenerate tails, chains, stars and high branching.
4. Verify the meaning of the paper's printed leaf recurrence. If it counts something other than actual tree leaves, define both measures explicitly and prove the bound needed for the final theorem with *actual tree leaves*; do not substitute one for the other by name.
5. Prove a suitable bound in terms of `n * min(depth, leaves)` (up to the constants or lower-order terms actually supported), or document a demonstrated counterexample and a corrected theorem before proceeding.

**Gate B:** a closed theorem bounds the actual state set in the tree parameters that appear in the claimed asymptotic result. It has no unexplained combinatorial hypothesis. Counterexamples or corrections are preserved as small mathematical tests.

### C. Optimality of the dynamic program (embedding and isomorphism)

1. Identify the exact paper-level LCBE (balanced embedding) and LCBS/LCSI
   (balanced isomorphism) result contracts, and distinguish them from the
   NetworkX-facing routine names `Solver::emb` and `Solver::iso`.
   Define each optimum independently over valid finite witnesses or a proved
   equivalent finite characterization. Do not assume the two recurrences
   solve the same problem.
2. Define the paper's numeric recurrence as a *separate* executable function; prove the recurrence returns that independent optimum by soundness, completeness, and well-founded induction.
3. Give an explicit witness-producing algorithm for each promised solver;
   prove its returned witness is feasible and has the optimal score, including
   base cases, order constraints, and tie choices. Show tree witnesses and
   sequence-index witnesses correspond.
4. Prove the resulting tree witness solves the contraction-based MCES problem using Gate A, without defining `MCES` via the DP result.

**Gate C:** checked theorems establish the specified embedding/isomorphism optima and independently valid tree witnesses for every covered algorithm. Unfolding a recurrence is insufficient.

### D. Cost semantics and the 2004 complexity claim

1. Define the DP state domain, transition count and a concrete work model for state construction, table operations, coding/decoding and witness reconstruction.
2. Prove termination, state uniqueness/canonicalization, and that each required state is evaluated a bounded number of times.
3. Relate the state count to Gate B, and the work counter to the algorithm of Gate C.
4. Prove the advertised form `O(n1*n2*min(d1,l1)*min(d2,l2))` **only if** its operations and data-structure assumptions justify it. Explicitly distinguish expected-time hashing from deterministic worst-case operations; state memory use separately.
5. If actual implementation operations entail an extra logarithmic or representation factor, prove that bound and document the difference. Do not force a desired asymptotic statement by silently postulating constant-cost operations.

**Gate D:** the complexity theorem names an executable algorithm and cost model and has no free assumption asserting the very state-size inequality it intends to prove.

### E. Rust via Charon/Aeneas

1. Run an **early small feasibility spike** translating a real Rust tree/sequence state operation to Lean, establishing toolchain versions and supported data representations before a major Rust rewrite.
2. Create a small safe Rust core independent of PyO3, Python callbacks, runtime trait objects, concurrent scheduling and third-party container internals. Keep the public I/O contract explicit and deterministic.
3. Translate the maintained Rust source using pinned, compatible Charon/Aeneas revisions and compile its generated Lean; do not manually modify generated definitions to obtain a proof.
4. Prove representation/validation, index safety, memo-table invariants, DP transition correctness and witness reconstruction against the independent Lean specification.
5. Establish an end-to-end theorem about the **translated Rust entry point**: for accepted inputs under stated bounds, it succeeds (or returns only documented errors), its witness is valid and its score is optimal.
6. Add a clean regeneration check comparing extracted Lean against checked-in/generated proof dependencies. Include `#print axioms` or an equivalent audit on the public theorem's dependencies.

**Gate E:** Rust source -> Charon/Aeneas -> generated Lean -> proved refinement to the independent optimum, with reproducible tool pins and documented trusted boundaries. An extraction-only demo does not meet the gate.

### F. Performance and application integration

1. Preserve existing Python, Cython and PyO3/Rust implementations as unverified comparison baselines; do not replace them just because the proof code is complete.
2. Use an independently enumerating contraction oracle for tiny instances and independent witness validation for all sizes. Differentially compare optimal values across all available backends; permit different equally optimal witnesses.
3. Measure CPU time, allocations, peak RSS, state counts, memory and scaling on chains, stars, balanced trees, combs, brooms, random trees and existing applied module-tree cases.
4. Profile before optimizing. Each optimization requires a refined correctness argument or a verified equivalent representation, and a before/after benchmark.
5. Integrate the verified Rust core behind the existing NetworkX-facing ordered-tree API with explicit conversion/witness mapping. Treat labels, affinities and weighted scoring as separately specified extensions.
6. Keep the unordered weighted algorithm family distinct; its matching and distance-penalty semantics are outside the 2004 proof.

**Gate F:** verified Rust matches the independent oracle in its feasible exhaustive domain, is usable through the intended API, and has measured performance sufficient to justify its use.

## 5. Work packages and proposed order

| ID | Deliverable | Depends on | Done when |
| --- | --- | --- | --- |
| W0 | Stabilize the fresh Lean build, toolchain and baseline inventory | none | `lake build` passes from clean checkout; dependency lockfile and exact status recorded |
| W1 | Independent tree and contraction-based specification plus exhaustive oracle | W0 | edge/root conventions explicit, examples and small oracle checked |
| W2 | Fresh balanced-sequence definitions and full contraction/containment equivalence | W1 | Gate A |
| W3 | State decomposition mathematics, actual-leaf cardinality bound | W2 | Gate B |
| W4 | Independent DP optimality and witness construction | W2; W3 for paper theorem chain | Gate C |
| W5 | Algorithm-specific cost semantics, corrected Theorem 3 | W3, W4 | Gate D |
| W6 | Minimal Aeneas translation spike and pinned workspace | W0; parallel to W1-W3 | a real Rust function translates, generated Lean builds, basic refinement theorem checks |
| W7 | Proof-friendly Rust implementation and proof of translated entry point | W4, W6 | Gate E |
| W8 | Complexity refinement for actual Rust data structures, if needed | W5, W7 | quantified and proved cost claim within stated model |
| W9 | Independent tests, API adapter, benchmarks, optimization | W7 | Gate F |
| W10 | CI, theorem inventory, full paper coverage audit and documentation | all | fresh checkout reproduces results and claims |

Work can be parallel where dependencies permit, but **never let Rust implementation details dictate the abstract theorem statements**. Conversely, do not design an elegant but non-extractable Lean-only algorithm and assume an implementation proof will be easy afterward. Use the early W6 spike to inform representation decisions.

## 6. Assurance ledger

Track accepted claims in a small `proofs/PROOF_STATUS.md` once there are actual proof targets. Give exact theorem identifier, hypothesis list, source file, build command and classification: `specified`, `proved`, `conditional`, `extracted`, `tested`, or `open`. An item is `proved` only after the fresh Lake build and theorem-dependency review.

Status after the user-reported successful local `lake build` (dependency audit still pending):

| Target | Status |
| --- | --- |
| Independent tree/embedded-subtree specification | compiled in the reported local build; paper-semantics equivalence and axiom audit pending |
| Tree/Dyck encoding and forward contraction soundness | compiled locally (maintainer-reported) |
| Converse contraction/completeness and two-way equivalence | authored; local build pending |
| Equivalence to the paper's exact annotated containment relation | open |
| Paper combinatorial results and actual-leaf state bound | open |
| LCBS DP optimality vs. independent optimum | open |
| Tree witness correctness | open |
| Algorithm-specific Theorem 3 complexity | open |
| Charon/Aeneas extraction of new Rust core | open |
| Generated-Rust-to-spec refinement | open |
| Rust valid-input safety and error contract | open |
| Python adapter correctness | open |
| End-to-end benchmark comparison | open |

**No theorem from the retired proof tree is part of the new trusted result.** We do not inherit its build status or proof claims. Keep legitimate external assumptions (Lean kernel, standard mathematics libraries, tested translation-tool semantics and explicitly modeled data-structure contracts) visible. The goal is no local `sorry`, `admit`, arbitrary `axiom`, or opaque unverified operation in the accepted correctness chain.

## 7. Repository layout: build as needed

```text
proofs/
  README.md
  lean-toolchain, lakefile.toml, lake-manifest.json
  SubtreeProofs/
    Paper2004/
      OrderedTree.lean
      BalancedSequence.lean
      Containment.lean
      Decomposition.lean
      Cardinality.lean
      Optimality.lean
      Complexity.lean
    Algorithm/
      DP.lean
      Witness.lean
      Correctness.lean
    Rust/
      Generated/                 # reproducible translator output
      Refinement.lean
      Safety.lean
rust/
  crates/
    lozano_valiente_core/       # future proof-friendly crate
  src/lib.rs                    # existing PyO3/backend; unchanged by proof reset
networkx_algo_common_subtree/  # existing API and independent Python reference
```

This is a responsibility map, not a mandate to create empty modules. Make choices after W1 and W6, and avoid speculative compatibility shims and generic loose symbol names. There should be one canonical specification and one accepted production proof chain, not a series of `v2`, `v3`, `final` modules.

## 8. Testing and release gates

- **Mathematics:** enumerate all small ordered trees/pairs within a fixed practical bound; compare DP with a distinct contraction-based oracle and validate each reported witness. Retain minimized counterexamples, especially those that separate actual leaf counts, order constraints, and root semantics.
- **Rust:** tests for valid/invalid encodings, score boundaries, equal-score ties, overflow/index handling, degenerate tree shapes, reproducibility and any deterministic container invariants.
- **Formal:** `lake build`, explicit theorem dependency/axiom audits, generated-code regeneration, Rust test/fmt/clippy, and a clean-build compatibility matrix pinned after the W6 spike. The critical theorems must compile without importing legacy code.
- **Performance:** compare against actual Python/Cython/PyO3 baselines with recorded hardware, versions, flags, warmup policy, distributions and state counts. Prove asymptotics through the model; report measured performance separately.
- **Integration:** verify the ordered API's representation and output mapping. Do not silently change semantics of unordered, labeled or weighted calls to match the new core.

Keep CI proportional to real failures: target core invariants and regressions, avoid source-text/process meta-tests, and keep full exhaustive or large benchmark runs optional outside appropriate release jobs.

## 9. First execution cycle: concrete acceptance checklist

1. Preserve the passing `OrderedTree.lean` foundation. Reproduce `lake build`
   on Lean 4.35.0 from a fresh checkout, inspect accepted theorem dependencies
   with `#print axioms`, and keep `PROOF_STATUS.md` current. The first local
   build success has been reported; clean-checkout reproducibility is still open.
2. Pin toolchain and commit `lake-manifest.json`. Add a minimal CI job running
   the actual Lean build (not a test of file text or theorem names).
3. Write a tiny **contraction-enumerating** oracle independent of the Dyck-word
   recurrence. Fix root conventions and examples for contraction of a root
   child, a nested edge, and sibling splicing. Exhaustively compare true leaf
   and edge counts on small trees.
4. Prove tree/forest encoding and decoding round trips, with semilength, edge,
   depth, and true-leaf invariants. Then prove both directions of sequence
   containment versus the tree contraction closure.
5. In parallel, translate a small real Rust state/encoding operation with
   Charon/Aeneas. Compile the generated Lean and prove a nontrivial
   representation/refinement lemma; pin the compatible revisions.
6. Derive decompositions and finite state sets `D`, `R`, `S` and the true-leaf
   cardinality bound, with exhaustive discriminators for chains, stars, and
   unary cases.
7. Prove independent LCBE/LCBS numeric DP optimality and witness correctness,
   then connect exact operation counts to the corrected complexity statement.
8. Isolate a proof-friendly Rust core without disrupting the currently
   integrated optimized baseline; prove its translated entry point correct,
   benchmark on adversarial and practical trees, then integrate deliberately.

The next milestone is **a successful local check of the converse theorem,
then an independent contraction oracle and the paper-containment crosswalk**, with axiom auditing and clean-checkout CI for the
now-compiling foundation. Build success alone leaves the central mathematical
correspondence and the paper algorithm unproved.

## 10. Sources

- Lozano & Valiente (2004): https://www.cs.upc.edu/~antoni/subtree.pdf
- Aeneas / Charon project: https://github.com/AeneasVerif/aeneas and https://github.com/AeneasVerif/charon
- Aeneas getting started (verify commands against pinned revision): https://github.com/AeneasVerif/aeneas/blob/main/documentation/getting-started.md
- Existing application code, tests and benchmark suite in this repository (not a source of mathematical truth)

The historical `proofs` branch remains accessible through Git, but it is intentionally excluded from the new work plan and formal dependency graph. Cross-paper reuse and verification principles live in the [program charter](verified_common_subtree_research_program.md).
