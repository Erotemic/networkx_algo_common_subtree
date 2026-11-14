# Droschinsky, Kriege, Mutzel (2016 and 2018): verified Rust and Lean plan

Status: independent graph/path specifications and finite optima proved; reference semantics tested; paper DP/optimization proofs open
Updated: 2026-11-14
Program charter: [Verified common-subtree research program](verified_common_subtree_research_program.md)










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
the published `O(n^2 Delta)` operation bound under explicit arithmetic and
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
| D5 | 2016 optimized matching updates and operation bound | D4 | Verified paper-specific `O(n^2 Delta)` assumptions and actual work |
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
