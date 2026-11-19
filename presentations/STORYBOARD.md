# Narration and mathematical storyboard

**Audience:** researchers and engineers comfortable with recursion and graph
algorithms, but unfamiliar with common-subtree variants. **Delivery:** narrated
lecture with 14 independent Manim chapters, or click-advanced `manim-slides`
scenes. The following is a substantive narration guide, not just captions. Each
chapter has a question, a worked example, a mathematical claim, and a transition.

The written equations follow the mathematical **operational** definitions and
relevant checked Lean source in the 2026-11-14 repository snapshot. The full
paper texts are cited in `REFERENCES.md`. Where a scene draws a simplification,
that is indicated in these notes.

## 1. AllProblems — three families, three different feasible sets

**Question:** What does it mean for two trees to share structure?

A tree is a particularly favorable restriction of the general common-subgraph
problem, but there are several inequivalent meanings of “common.” If the
children of every vertex are ordered, we cannot permute them to improve a
mapping. If the children are unordered, we can. If intermediate vertices are
allowed to disappear along matched paths, we get a topological embedding,
which needs extra rules to distinguish allowable skips from false matches.

The 2004 ordered-tree algorithm uses *edge contraction*. In the 2016 weighted
common subtree isomorphism algorithm, two matched subtrees are locally
isomorphic: corresponding selected edges stay actual edges, and a collection
of child branches is paired by a weighted bipartite matching. The 2018
embedding problem allows longer paths, but charges for intermediate skipped
vertices. Neither the 2016 nor the 2018 problem should be silently presented
as equivalent to the 2004 ordered embedding problem.

**Transition:** Let us start with a tree representation that makes the ordered
case amenable to dynamic programming.

## 2. OrderedContraction — the operation that defines the order

**Question:** Which structures can we obtain by contracting an edge?

Take a rooted tree, retain its root, and select a non-root vertex. Contract its
incoming edge. The selected vertex disappears, but its children remain, spliced
into its parent's child list at exactly the same position. Every sibling order
not involved in the contraction remains unchanged. Repeating these operations
defines the embedding relation. A single edge contraction reduces the number
of edges by one. Its reflexive-transitive closure includes the original tree
and the one-vertex tree.

In the scene the three-edge tree has root `r`, child `a`, and grandchildren
`b,c`. Contracting the *internal* edge `r-a` removes `a` and splices its two children
`b,c` into the root, yielding the sibling forest encoded by `0101`. The scene
reveals the selected edge, the resulting tree, and the balanced-word change
with separate clicks. Labels in this
chapter are visual IDs, *not* semantic compatibility constraints. The proof language
should speak of structural positions, not depend on these arbitrary names.

This operation is closely related to the deletion used in ordered tree edit
distance, but the objective of maximum common embedding is different: we seek
a largest structure obtainable in both trees, not a minimum-cost edit script.

**Transition:** How can all these contractions be represented by operations on
balanced strings?

## 3. BalancedWords — encode traversal as a Dyck word

**Question:** Why would a string algorithm solve a tree problem?

Traverse each edge in depth-first order. Write `0` as we descend an edge and
`1` on return. Every non-root vertex contributes exactly one balanced pair.
The resulting string has equal numbers of zeros and ones, and every prefix has
at least as many zeros as ones. Such strings are Dyck words. Conversely, given
a Dyck word, a stack can reconstruct an ordered forest under an implicit root.
The encoding is a bijection under that convention.

The tree shown has one child `a` whose children are two leaves `b,c`, giving
`001011`. The three `0` characters correspond to its three edges. Its
semilength is three. Explain why the encoding is *not* treating the preserved
root as a fourth pair: one pair per edge is the convention used here.

The first-return decomposition writes every nonempty Dyck word uniquely as
`0 x 1 y`. Here `x` encodes the subtree below the first child, and `y` encodes
the remaining sibling forest. This decomposition is the main algebraic tool in
the 2004 recurrence.

**Transition:** The key theorem says the structural contraction relation has
an exact string counterpart.

## 4. DeletionIsContraction — containment is a structural theorem

**Question:** Does deleting a matched pair capture precisely one contraction?

Deleting a matched `0...1` pair while retaining its interior corresponds to
removing the associated non-root vertex and splicing its children upward. For
the displayed example, `001011` can become `0011` by deleting one of the leaf
pairs. If we instead deleted the outer pair for `a`, its two children would
become siblings, yielding `0101`. Both are legitimate contractions, but they
produce different ordered trees.

A proof must establish both directions: every tree contraction gives a legal
word deletion, and every legal word deletion decodes to a tree contraction.
The current Lean development contains both directions and the encoded
reflexive-transitive-closure equivalence. We should not define tree embedding
*as* string containment and then celebrate the correspondence as a theorem;
that would be circular relative to the desired paper interpretation.

There is a source-history complication. The 2004 paper's literal printed
recursive Definition 2 does not admit every one-pair deletion that the
operational relation admits. The repository contains a formal counterexample
and a separate audit. Explain that we use the operational definition,
consistent with the intended edge contractions and Lemma 8 recurrence, while
preserving the printed relation as a distinct historical object.

**Transition:** Now the embedding optimization can be solved by deciding what
to do with the first matched pair.

## 5. OrderedRecurrence — derive all three branches

**Question:** How can an optimal common embedded word begin?

Let `a = 0 x 1 y`, `b = 0 u 1 v`, with `x,y,u,v` themselves balanced. If the
first edges of both input words are retained as the first edge of a common
solution, we keep that pair and independently optimize the inside and outside:
`1 + L(x,u) + L(y,v)`. The leading `1` counts the paired first edge.

If the first edge of `a` does not survive, contract it and solve the reduced
instance `L(x+y,b)`. Symmetrically, if the first edge of `b` does not survive,
contract it and solve `L(a,u+v)`. Taking the maximum of these three values is
the recurrence in Lemma 8, using the operational semantics of the problem.
The base case is zero if either word is empty. The scene computes a small
example explicitly: for `a=001011` and `b=0011`, the three candidate scores
are `2`, `1`, and `1`. The first branch wins, and the common embedding
score is two edges.

It is important to explain that the recurrence is not a stand-in for the
mathematical specification. The independent specification is the maximum
semilength of a Dyck word obtainable by contractions from **both** inputs.
Soundness says each constructed candidate is feasible. The upper bound says
that any feasible common word must fall into one of the three branches; by
induction, its semilength cannot exceed the chosen maximum.

The implementation may memoize distinct subproblems, but memoization alone
does not prove the published runtime bound. Cost depends on the number of
states, how they are represented, the cost of dictionary operations, and
witness reconstruction.

**Transition:** Let us separate the proof obligations from their algorithms,
so that later Rust verification can reuse the established mathematics.

## 6. CorrectnessAndComplexity — mathematical correctness versus time

**Question:** What exactly has been proved when the recurrence is correct?

State the mathematical optimum independently as a maximum over all common
operational embeddings. The constructive Lean theorem proves that the paper
recurrence produces a common word and has semilength at least as large as any
other common word. Both directions of the Dyck/tree equivalence transfer this
result back to rooted ordered trees.

The combinatorial complexity analysis is a separate argument. A bound on the
number of distinct decomposition states does not automatically bound an
implementation's operations: a linked-list memo table, an expensive hash
function, cloned witness trees, or Python callbacks can change actual runtime.
The 2004 theorem additionally includes real tree depth and leaf-count
parameters, which must be measured from trees rather than from a surrogate
sequence recurrence. The repository corrected a discrepancy in the printed
leaf recurrence and carries detailed theorem-status ledgers.

The contrast to carry forward is concrete: a formally proved optimum is an
assurance about **answers**, while a formal complexity theorem is an assurance
about **resources under a stated model**. Performance benchmarks measure
actual costs for the implementation and machine being tested.

**Transition:** The original code contains further functionality that needs its
own mathematical contracts.

## 7. AffinityExtensions — algorithm extensions and mapping semantics

**Question:** How do labeled and weighted inputs change the problem?

The author's Cython and Python implementations introduce affinity or
compatibility functions for node pairs, alongside token mappings and witness
reconstruction. For a fixed feasible mapping, a node-weight sum is a natural
illustration: `score(M) = sum a(u,v)` over matched vertex pairs. The actual
extension specification should be pinned from the current API and code,
particularly whether pair weights are boolean compatibility, real-valued
rewards, or a combined model with edge weights. Do not invent semantics from
this illustrative formula.

An algorithm can have a correct unweighted recurrence and still have incorrect
extension handling: negative scores, asymmetric affinities, numerical
precision, and mapping back to original input IDs all affect correctness.
The existing Cython code is evidence of intent, not an authoritative oracle.
Independent small cases and the user-authored original behavior must be
reconciled into an exact contract.

Distinguish ordered *embedding* from ordered *isomorphism*, including cases
where the root or first edge is retained or rejected. Explain to an audience
why the “same” state table is not automatically a valid implementation of both
problems.

**Transition:** Order changes the recurrence fundamentally. Without sibling
order, selecting compatible branches becomes a matching problem.

## 8. WeightedUnorderedMatching — the 2016 recurrence

**Question:** If child order does not matter, how do we choose branches?

Fix a pair of matched roots `(u,v)` in the two unordered input trees. Each
child branch of `u` can match at most one child branch of `v` and vice versa.
A candidate child pair `(a,b)` contributes the corresponding edge similarity
plus the best continuation score for the two child subtrees. This gives a
weighted *partial* bipartite matching problem on the children, with forbidden
pairs allowed and unmatched children permitted. The displayed equation is the
fixed-root recurrence, *not* the entire unrooted algorithm.

For the displayed 2-by-3 weight matrix

```
8  1  4
3  7  2
```

the optimal matching is row 0 to column 0, row 1 to column 1, total weight
`15`. The values are deliberately simple aggregates of edge rewards and
continuation scores. The independent example checker enumerates all partial
matchings and returns that optimum. For signed weights, it can be optimal to
leave some child branches unmatched.

The unrooted problem still has to consider orientations and root choices.
The 2016 paper makes its main efficiency advance by reusing information among
related matching instances rather than solving all of them from scratch.

**Transition:** Why is a generic assignment solver for each subproblem not
the same as the published fast algorithm?

## 9. SparseMatchingOptimization — structure is a computational resource

**Question:** How can a family of similar weighted matching problems be cheaper
than an unrelated family?

A naïve implementation might use a Hungarian-style solver independently for
every root/child pair. It may be mathematically correct and a good reference,
but does not automatically attain the 2016 asymptotic bound. The paper uses
structural relations among the matching instances. Warm starts, reusing
potentials or augmenting-path information, and carefully handling omitted
vertices offer the leverage needed for stronger bounds. The scene is a
*conceptual* diagram of reuse, rather than a statement of a specific code
path already implemented in the repository.

State the paper's general bound `O(n^2 Delta)` and explain the parameters:
`n` measures input size at the relevant scale; `Delta` is maximum degree.
The result concerns weighted unordered common subtree isomorphism. To claim
our own Rust implementation achieves it, we must inspect its actual matching
engine, verify all recurrence and root-orientation logic, and measure the
resulting implementation on high-degree and realistic instances.

**Transition:** The 2018 variant changes not only the optimization method but
the set of admissible embeddings and the score assigned to a path.

## 10. TopologicalDistancePenalties — a rule with an important edge case

**Question:** What if a matched abstract edge corresponds to a longer path?

A topological embedding maps neighboring vertices of the abstract common tree
to endpoints of paths in each input tree. Interior vertices of those paths
may be skipped, subject to structural compatibility constraints. Each
abstract edge is counted once, and different abstract edges cannot share
prohibited interior vertices.

Use the smallest example: one tree has two selected vertices connected by
one edge; the other has the same selected endpoints connected by two edges
through one skipped interior vertex. Suppose each matched endpoint contributes 1, the direct-edge reward is
1.5, and the skipped vertex penalty is 0.25. When both mapped paths have one
edge, the example scores `1 + 1 + 1.5 = 3.5`. When one path has length two,
the edge reward disappears, and the score is `1 + 1 - 0.25 = 1.75`.
The 2018 published Definition 4 awards edge similarity only when **both**
corresponding paths are direct edges. A previous repository implementation
incorrectly credited this reward on a longer path; the new example shows why
that would change the objective.

Clarify that the equal-weight example isolates the rule; it is not a general
optimality proof. The real mathematical specification must also ensure that
the selected vertices produce a valid skeleton and that skipped branch points
do not create illicit embeddings.

**Transition:** How much of this mathematics has to survive translation into
optimized Rust and Python wheels?

## 11. MappedAndSkippedStates — the 2018 rooted dynamic program

**Question:** How does a dynamic program decide whether to map the current
vertices or skip intermediate vertices?

The rooted reference evaluator maintains *two* quantities at each vertex
pair. The mapped state `M(u,v)` assumes the current endpoints are both selected
and scores their node match plus the optimum partial matching of their child
branches. The child-pair contribution may be the direct-edge reward plus a
mapped continuation, or a skipped-path continuation in which earlier vertices
were bypassed.

The skipped state `S(u,v)` makes a different structural decision: advance
through a child on one side while the other side is held in place, and pay a
single-vertex distance penalty. One advances repeatedly to represent longer
paths. It is essential to keep the two states separate so that an edge label
reward is awarded only for direct edges, rather than incorrectly added on top
of a skipped-path penalty.

The displayed formulas summarize the actual `step` definition in
`Droschinsky2018/RootedDynamicProgram.lean`. Its child assignment currently
uses an exhaustive finite matching solver, making this a correct *reference*
evaluator under its proof assumptions. The optimized 2018 algorithm exploits
matching structure and sparsity to obtain the published bounds. This scene
must not imply the implementation already meets them.

The generic weight functions, infinite penalty case and valid skeleton
restrictions are covered in the Lean specification rather than fully displayed
in the introductory formula. Include these details in a technical seminar.

**Transition:** Both the 2016 and 2018 recurrences now have an independent
specification. What does it take to verify the actual Rust source that people
will run?

## 12. ProofBoundary — what verified software means

**Question:** How do mathematics, algorithms, and executable code correspond?

Independent feasible mapping definitions and scoring functions answer “what
is the problem?” A correct recurrence answers “what mathematical computation
finds its optimum?” Lean formalization can justify each of those theorems.
Aeneas/Charon translation takes actual Rust source into Lean semantics; a
refinement theorem then connects the source function's result to the
mathematical contract. This is stronger than proving an unrelated Lean
reference implementation has the right result.

Even that does not automatically cover Python input conversion, callback
behavior, serialization of witnesses, shared-object packaging or all
optimized production paths. There can be a verified reference solver and a
faster legacy solver exposed as the default. A complete verified release
needs the **actual chosen runtime implementation** inside the assurance
boundary, or a clearly specified trusted envelope.

Read the current `proofs/PROOF_STATUS.md` when preparing a talk. The November
14 snapshot already has proof chains for the ordered recurrence, matching,
several actual Rust entry points, and 2018 recurrences. It does not justify
claiming every published optimized complexity result or Python-wheel boundary
is proved. Give theorem names and version pins when making public claims.

**Transition:** A correct and fast implementation could become a research
contribution if it helps on a real, well-defined task.

## 13. ApplicationExperiment — structural code comparison pilot

**Question:** Can these algorithms do better on a task where tree structure
matters and we have strong baselines?

Parse code revisions into abstract syntax trees using a reproducible parser
such as Tree-sitter. Preserve stable node types and relative order. The
candidate use case is finding structure that persists across nontrivial code
edits, including inserted wrappers and moved or expanded subtrees. Ordered
embedding, possibly with typed affinities, provides a particular exact
structural comparison objective. It is worth investigating whether that
objective yields better mappings or faster useful retrieval on some classes
of edits than existing approaches.

The baseline set must be strong: APTED for optimal ordered tree edit distance,
GumTree for practical AST differencing, and a recent refactoring-aware
mapping baseline such as RefactoringMiner. **These methods solve different
objectives.** A raw objective score from our embedding must never be compared
to APTED edit cost as though smaller or larger meant the same thing. Measure
on a shared downstream task: node-mapping precision/recall against reviewed
mappings, edit localization quality, structural change detection, or latency
at a target quality threshold.

For a paper, split by code projects or commits to prevent leakage, report
input-tree shape distributions, control node labeling and parsing, include
strong baselines with their native optimizations, and publish failures as well
as successes. This is an experimental hypothesis, not a result.

**Transition:** What sort of contribution would withstand a reviewer who knows
the old subtree and AST algorithms?

## 14. PaperContribution — distinguish established theory from new evidence

**Question:** Where could new work actually be located?

The three original papers have already established their mathematical problem
families and core optimized recurrences. Reimplementing them is engineering
work and possibly useful open-source software, but one should not claim
novelty merely because the old algorithms are now written in Rust. A strong
paper could instead combine a rigorous source-to-specification verification
story, identified and repaired mathematical or specification issues,
performance improvements demonstrated against well-tuned baselines, and a
new application with measurable value. Any newly introduced affinity model,
witness policy, or optimization requires a precise contract and comparison to
closest prior work.

There are several plausible paper narratives: (1) a verified implementation
paper describing proof architecture and actual Rust assurance, including
optimization and packaging boundaries; (2) an algorithm engineering paper if
new techniques produce reproducible speedups against strong native baselines;
(3) an applied structural-matching paper if a new task, dataset, metric, or
meaningful empirical result appears. These are alternatives, not three
claims we can already make.

The next scientific step is a pilot that fixes the dataset, problem contract,
baseline implementations, and primary outcome **before looking for positive
results**. If the pilot is negative, it still tells us which objective is
appropriate and whether the presentation should emphasize verification over
application superiority.
