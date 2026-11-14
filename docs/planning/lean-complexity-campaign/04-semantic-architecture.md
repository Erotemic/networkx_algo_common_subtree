# 04. Semantic architecture

## 1. Three independently reviewed objects

Every substantial complexity claim connects three objects:

1. **A mathematical specification**, such as maximum embedding score or a map lookup relation.
2. **An executed computation in a named semantics**, such as the existing memo evaluator, a charged program, an explicit state machine, or an instrumented Rust/LLBC model.
3. **A resource bound**, derived from local contracts and structural mathematics.

The value specification must not be defined as "whatever this evaluator returns." An execution-cost theorem must not take the desired whole-program bound as an unexplained field. The bound may be conditional on primitive contracts, but each contract must name an operation, its inputs/state, the resource model, and its proof or assumption status.

The campaign should initially support a deterministic, sequential, terminating computation with explicit failures. Nondeterminism additionally requires demonic totality: every maximal execution must terminate in an allowed outcome, and every such execution must satisfy the bound. Existence of one terminating branch is insufficient. Use the backend's total-correctness semantics if it supports this. A broad nondeterministic semantics is not a prerequisite for a deterministic client.

## 2. The minimal mathematical interface

Conceptually let

\[
\operatorname{Run}(p,x,\sigma_0,y,\sigma_f,\tau)
\]

mean that program `p`, input `x`, and initial state `sigma_0` execute successfully to value `y`, final state `sigma_f`, and an ordered list of resource events `tau`. Events are **occurrences**, not unique labels. Different occurrences may have the same descriptor. An explicit trace is a specification device; production execution need not allocate it.

For an event price `price : Event -> Nat`, define

\[
\operatorname{work}_{price}(\tau)=\sum_{e\in\tau}price(e).
\]

A resource specification must establish existence of a successful run under its success precondition, correctness of all relevant results, and a bound for every allowed run. Where errors are legitimate outputs, use an outcome type and specify their costs too. A theorem only quantifying over successful runs can be vacuous if the program never succeeds. Existence of one successful run fixes that particular vacuity but still does not exclude a diverging or stuck alternative in a nondeterministic semantics. Total correctness also needs the separate all-executions termination/progress property. Restrict the first API to deterministic execution unless that property is supplied by the backend.

The final public API may use a backend's own judgments instead of this syntax. The adapter must prove an equivalence or implication with this meaning, rather than duplicating the backend evaluator merely to match the notation.

## 3. Resource vocabulary

Start with natural-number work and the smallest useful event taxonomy. A proposed initial taxonomy separates:

* dictionary lookup, equality checks inside lookup, insertion and resize;
* word/token access, concatenation, slice materialization and copy;
* loop/body visits, control tests and function-entry overhead where charged;
* matching scans, comparisons, dual updates and augmenting-path changes;
* allocation/free events for the separate space model.

Do not simultaneously charge an abstract dictionary event and all its concrete comparisons at full price unless the sum is deliberately an upper bound and that double accounting is documented. The clean design is a hierarchy: abstract requests refine to concrete event blocks, then are priced once at the chosen boundary.

A finite `CostVec` is useful when operation prices are fixed independently of execution state. A count vector by itself cannot express that the fifth lookup scans a larger table than the first. Use event descriptors carrying sizes or a stateful/amortized primitive contract. A vector of "lookup count" and "total scanned entries" is also valid if its computation is justified.

Do not force peak space or parallel span into the additive work algebra. Those resources have different composition laws.

## 4. Primitive contracts and adequacy

A primitive contract has four parts:

* an input/state precondition and representation invariant;
* a result/final-state relation to an independent specification;
* a resource claim for the primitive's concrete execution;
* a preservation/frame property needed by its callers.

For example, an association-list lookup returning the first matching value may have a cost bound depending on table length and per-key comparison costs. Its result relation states agreement with finite-map semantics under a no-duplicate-key invariant, or explicitly states first-match semantics when duplicates are allowed. These are different contracts.

The expensive-callback loophole must be closed at the interpretation boundary. A higher-order body can only be treated as free when the cost model deliberately counts some narrower resource, or when an independently proved contract bounds its evaluation. Sealing data access is useful engineering, but a private constructor alone does not prove a source-level runtime bound.

arlib's `ExactRealizes` already separates representation correctness from equality of opcode tallies [L02]. Use such existing structure where it fits. `TimeM` explicitly records trusted annotations [L03]; it becomes execution-linked only with a further adequacy relation. The campaign's comparison must respect those distinctions rather than treating either representation as intrinsically sufficient or unusable.

## 5. Composition and user-facing specifications

Provide compositional rules for sequencing, conditionals, loops/folds, recursion and subroutine calls. Branching pays for the branch actually taken; a uniform bound may take a maximum over alternatives. Sequential bounds must account for the actual intermediate state and result sizes.

An implementation may have exact cost `c_impl(x)`, while a client uses an opaque envelope `c_spec(size(x))`. Prove the execution specification using that envelope and separately prove its asymptotic domination. Retain enough monotonicity to substitute size bounds safely. This is the role played by abstract cost specifications in [R01]; it is not a reason to hide input constraints or uniformity of constants.

An amortized subroutine specification must expose pre- and post-potential:

\[
C_{run}+\Phi(\sigma_f)\le b(x)+\Phi(\sigma_0).
\]

A caller can compose these without knowing exact internal constants. It cannot discard the post-potential and then reuse the pre-potential in another branch. Ownership or an explicit global ledger enforces that restriction.

## 6. Cost-aware refinement

Value refinement and resource refinement are separate fields. A cost-aware relation between a concrete and abstract computation should include a state/value representation relation and a bound on the concrete event block implementing each abstract action. The bound may depend on the action's input and representation state.

For variable-cost primitive implementations, use a local inequality with potentials or a specific cost function, then sum it over the run. Avoid the naive claim that functional equivalence preserves asymptotic complexity: repeated recomputation is an immediate counterexample.

Stuttering requires care. A concrete step may leave the abstract state unchanged. It must still consume a counted resource, reduce a well-founded stuttering rank, or spend a finite potential according to a proved rule. Mapping arbitrary concrete loops to an empty abstract trace is not a termination or cost proof.

Composition of refinements should explicitly account for initialization, marshalling and finalization. If each abstract action has additive implementation overhead, that overhead is paid per action. It must not be collapsed into one global constant without bounding the number of actions.

## 7. Memoized recursion: the intended public boundary

A memoized body is a computation with two kinds of effects: local primitives and requests for other keys. The interpreter owns the cache. Clients do not mutate it directly. For a first implementation, require a well-founded dependency relation and no eviction. Later invalidation policies are separate theorems.

The initial cache must be sound relative to the current input environment. Semantic keys must distinguish all information on which the answer depends. A cache of values for an old input or changed scoring function does not satisfy this invariant merely because the key type is unchanged.

The interpreter must thread the updated cache through every child request. It inserts a completed value only after a successful body evaluation. A well-founded dependency proof prevents re-entry into an unfinished identical key; an explicit in-progress state can detect cycles but does not, by itself, solve cyclic equations.

Track a list of root requests, not just one root. Empty roots, repeated roots and a fully warm cache must have correct counts. Track actual dependency-request occurrences, including repeated requests to the same child. Enumeration/key-construction cost belongs to local work.

A theorem about this interpreter is C1. It becomes C2 when primitive/body interpretation is connected to operational execution; it becomes C3 for a particular source implementation after the source adapter is proved. Preserve those endpoints separately.

## 8. Batch computation and persistence

Batches have an explicit initial preparation, a sequence or branching family of jobs, and finalization. Shared data may be read repeatedly, but the construction cost is charged once only when the implementation actually reuses one prepared object. If the source clones a large structure for each job, cloning must appear in the trace and in the bound.

For a sequential warm-start family, the post-state of job `i` is the pre-state of job `i+1`; an ordinary potential theorem may apply. For sibling deletion problems each solved from the same baseline, that chain usually does not exist. Use an occurrence ledger and bound the multiplicity with which baseline resources are revisited, or use a valid ownership/debit model for the actual shared implementation.

The Droschinsky family theorem must identify what is reused: initial matching, dual labels, graph representation, frontier arrays, or precomputed scores. Each has a separate validity and cost-preservation obligation. "Related instances" is a description, not a complexity premise.

## 9. Space architecture

Define the requested space before choosing machinery. Possible meanings are live table cells, total allocation volume, abstract live words, maximum recursion depth, or physical heap use. They are not interchangeable.

For allocation/free traces, a useful mathematical profile records `(required initially live/owned amount, net change, peak additional live amount)`. With integer net change `d`, nonnegative requirement `r`, and nonnegative peak `p`, sequential composition obeys

\[
(r_1,d_1,p_1)\circ(r_2,d_2,p_2)
=(\max(r_1,r_2-d_1),\ d_1+d_2,\ \max(p_1,d_1+p_2)).
\]

The validity conditions include sufficient initial ownership and well-formed frees. This profile is only an abstract occupancy summary. Aliased values, shared structures and allocator residency need a representation theorem. Inspect arlib's space profile and exact-net assumptions before implementing a new one [L02]. GC-specific results [R11--R12] are relevant references, not ready-made Rust allocator specifications.

For a rolling DP schedule, the live set at each cut consists of retained inputs/results with future uses, not merely the number of states ever computed. Temporary matching workspace and output reconstruction must be added to table residency. The live-set theorem is a useful generic target; a Rust process-memory theorem is a different project.

## 10. Asymptotics and machine bounds

First derive an explicit inequality on valid finite inputs. Then package it with Mathlib filters. State which parameters vary jointly and which constants must be uniform. With trees, degree, depth, leaf count and vertex count obey constraints; the admissible domain must reflect them.

A fixed finite machine type makes a naive "as input tends to infinity" theorem vacuous or meaningless. For abstract asymptotics, use unbounded mathematical input sizes and a word-size family adequate to the input, or state a finite-domain explicit bound for the actual fixed-width implementation. Keep the relation between those two claims visible.

Use `1+n`, `max 1 n` or a separate small-input case when the cost includes initialization but the intended leading term can be zero. State nontriviality of the growth filter for an exported claim that is intended to express real asymptotic growth. Do not remove nonempty/size/overflow premises merely to make an `IsBigO` proof shorter.

## 11. Runtime instrumentation and trust

Ghost counters may be erased in the proof artifact, or realized by an executable instrumented variant used for testing. Either way, prove:

1. erasing instrumentation preserves the result and state relation;
2. each selected source operation contributes the declared counter event;
3. the counter bound follows from the generic/structural theory;
4. the extraction/source correspondence has the declared scope.

The first statement alone permits arbitrary undercounting. Testing small executions can detect a mismatch but does not prove the second statement. Source hashes and generated-file checks prevent applying a valid theorem to a different program.

The initial campaign need not establish hardware instruction counts. It must state an honest source operation model and justify its relation to the pinned source. A machine-level refinement such as [L05] or [R10] is an additional endpoint, not an automatic consequence.

## 12. Packaging

Keep a generic mathematical layer, a backend adapter layer, and local consumers. During experimentation these may live under the existing proof workspace, but import dependencies must point from consumers toward generic code. Candidate paths and public proof interfaces appear in [07](07-interfaces-and-proof-experience.md). The actual package name is chosen only after coordination and the first two independent clients.
