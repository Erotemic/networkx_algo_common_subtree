# 07. Interfaces and client proof experience

## 1. Status and purpose

The [actual-run work follow-up](evidence/memo-work-envelopes.md) now checks
local `WorkModel` laws, weighted finite envelopes and native Std.WP with two
clients. It resolves supplied final-trace caps for those currencies; remaining
local/source costs and the other size/substitution interfaces stay open.

A [checked native memo implementation](evidence/memo-interpreter.md) now realizes
the D7 body/cache/counting boundary and part of D8. Its report lists exact
modules, retained client obligations and limitations; W04 is still partial.
The sketches below remain proposals where no executed report identifies a
checked counterpart.

The snippets in this document are **uncompiled interface sketches**. Identifiers other than explicitly cited upstream names are proposals. They are intended to constrain the first implementation experiment, not to pretend that a library already exists. G0 must produce checked signatures against an exact dependency pin before implementation assignments rely on them.

The central usability test is this: changing a memo-table implementation should require a new primitive resource contract and realization proof, while leaving the dependency/counting proof intact. Changing a recurrence should require local correctness, closure, termination and request-work arguments, while preserving the generic interpreter proof. Neither change should force a client to unfold every primitive's implementation.

## 2. Public boundaries

Use four boundaries with one-way dependencies:

| Boundary | Public objects | What a client should not see |
|---|---|---|
| Backend semantics | Programs, runs, totality, result/state predicates, resource interpretation | A second independent definition of the same backend semantics |
| Resource contracts | Independent result relation, input/output size relation, budget, potential/ownership when needed | Exact implementation constants and instruction traces unless requested |
| Evaluation structure | Memo body, request effect, dependency rank, cache invariant; scheduled tasks or batch jobs | Particular trees, matching weights or Rust-generated declarations |
| Application adapter | Existing mathematical specifications and source realization | Generic modules importing a subtree algorithm |

Do not require every client to construct a new abstract machine. Prove the backend adequacy theorem once and consume its established program rules. A backend-independent mathematical lemma can quantify over events or finite traces; a semantic theorem must identify the particular interpreter to which it applies.

## 3. Minimal mathematical vocabulary

The following simple definition illustrates the intended meaning of work. Prefer an existing equivalent definition with an adapter if the backend has one.

```lean
-- Design sketch only; not compiled for this overlay.
def traceWork {Event : Type} (price : Event -> Nat)
    (events : List Event) : Nat :=
  (events.map price).sum
```

A repeated event remains repeated. Event payloads can contain an operand size, an address range length or a representation state summary. When prices depend on more than the event descriptor, use a transition-indexed price and prove that a projected descriptor is sufficient before discarding the state.

A finite-trace upper bound alone has the following shape:

```lean
-- Partial-bound predicate: deliberately does NOT assert termination.
def FiniteRunBound {State Result Event : Type}
    (Run : State -> Result -> State -> List Event -> Prop)
    (price : Event -> Nat)
    (Pre : State -> Prop)
    (Post : State -> Result -> State -> Prop)
    (budget : State -> Nat) : Prop :=
  forall s y t events,
    Pre s -> Run s y t events ->
      Post s y t /\ traceWork price events <= budget s
```

The production API must combine this with the chosen backend's totality/progress theorem. For deterministic execution, an adequate successful run and determinism can be enough. For nondeterministic execution, one successful run is insufficient: all maximal executions must terminate in an allowed outcome. Do not hide this distinction in a generic field named `sound : Prop`.

A total contract must also distinguish legitimate error results from stuck computation. An error-returning function can have a useful cost specification even when its success precondition fails. Decide whether the public theorem covers all supported inputs or only successful inputs; use an explicit outcome relation in the former case.

## 4. Contract shape and substitution

A resource specification should make these parameters visible, in a stable order:

1. program and semantic model;
2. input/state precondition;
3. independent result and output-state relation;
4. size relation needed by downstream calls;
5. resource budget, and incoming/outgoing potential if amortized;
6. totality and execution-adequacy evidence inherited from the backend.

A contract is about a **program**, rather than only about a function from inputs to abstract costs. An abstract cost function can be part of that contract, but its connection to execution is the theorem.

The basic client operations should be consequence, sequence, branch, finite fold, well-founded recursion, and framing. A loop rule needs a loop invariant, local budget/potential rule and termination evidence. It should not ask the client to manually prove a fresh list-sum induction on every use.

Subroutine substitution must transport output-size bounds. For example, a preprocessing routine returning an array of length at most `g(n)` followed by a scan with monotone envelope `h` gives the second-stage budget `h(g(n))`. A proof that the output merely has the right value does not provide this size bound. A stateful dictionary's size after insertion belongs in its postcondition.

For an amortized API, the result carries the post-state potential. The caller is allowed to consume that returned potential once. If the same persistent value is used by two future computations, the interface must state a valid split, delayed debit discipline or explicit cost of reestablishing the resource invariant [R05].

## 5. Memo-body interface

The first generic memoization API should support a body that requests dependency values through an interpreter-controlled operation. It should not expose direct cache mutation to the body. A body can perform charged local operations and can choose its next request using already returned values. This is enough for data-dependent recursion without demanding a statically known dependency list.

Required fields or theorems, regardless of representation:

| Obligation | Required content |
|---|---|
| Mathematical meaning | `valueSpec : Key -> Value -> Prop`, independent of the memo implementation; functionality when used |
| Termination | Well-founded relation on keys, with every actual recursive request decreasing it |
| Context | Frozen input/environment, or an explicit version in the cache key; no reuse across changed meanings |
| Local correctness | If requested values meet their specifications, the body returns a specified value |
| State closure | Every requested key lies in the declared finite reachable envelope |
| Request work | Bound on request **occurrences**, including repeated requests to one key |
| Local cost | Uniform bound over valid response histories, excluding separately charged recursive/interpreter work |
| Representation | Cache abstraction, sound initial cache, lookup and insertion resource contracts |

The interpreter supplies unique expansion and root-plus-request accounting. Multiple root queries and warm caches belong in the core statement, since they change the accounting and are needed by batched computations. Eviction, concurrent evaluation and recursive cycles do not belong in this first contract.

A finite static dependency list is a useful specialization. It must be a list/multiset when requests may repeat. A set is sufficient only with an additional no-duplicate-request theorem or when it serves merely as a closure envelope.

## 6. Desired proof shape for a new dynamic program

A client proof should assemble the following evidence, with the names here serving as a checklist rather than checked declarations:

```text
body_correct          requested values imply the recurrence result
requests_decrease     termination order
requests_closed       finite state envelope
requests_per_expansion
local_body_budget     includes actual local data operations
cache_resource_spec   representation and primitive costs
source_realization    program runs the certified computation
```

Then a library theorem derives expansion counts, total requests and a priced work expression. A final size-envelope theorem supplies the desired explicit upper bound. The Mathlib asymptotic corollary is a separate short proof.

For LV2004, `requests_per_expansion` should specialize to the existing four-request result. For edit distance, it should derive a grid-state count and three predecessor requests in the relevant body cases. The two clients must not share a hidden tree-specific key representation. For a sparse DAG client, the exported bound should depend on reached states and actual edges rather than requiring all possible states to be visited.

The source realization is not re-proved from first principles for every recurrence if the source actually uses a certified interpreter or a compositional source translation. If the source is a different handwritten evaluator, a local correspondence theorem remains necessary. The library should make that obligation explicit rather than pretend it disappeared.

## 7. Backend experiment interfaces

**arlib route.** Inspect `Charged`, `ExactRealizes`, primitive implementations and the existing RAM/event model [L02]. Use `ExactRealizes.bind` or a weaker cost simulation rather than recreate compositional correspondence. Determine which operands and data operations remain outside the charged model. Establish how the local source loop maps to that model.

**Timed-refinement route.** Inspect Lax62's NREST semantics, error/top behavior, time/data refinement and source IR [L05]. Test only the narrow import surface needed by the pilot. Check whether the result-specification gap recorded for its examples affects any theorem being reused; do not substitute executable-twin agreement for the local independent specification. Record the separate 4.33-to-4.35 compatibility issue.

**`Std.WP` route.** Lean 4.35's `vcgen` and generalized WP infrastructure can provide the front end [L04]. Supply a sound cost-aware interpretation and primitive specification lemmas. Investigate whether a deep embedding is the simplest way to account for control flow. The tactic itself does not choose an adequate time model.

**TimeM baseline.** Use CSLib's representation to test interchange and quantify the missing adequacy obligations [L03]. An intentionally simple baseline prevents a large backend from winning merely by having more modules. A source adequacy theorem can make a TimeM-based interface sound; the annotation type alone cannot do that.

**Iris route.** Add it to the comparison when ownership or persistence is an actual blocker [L06]. First audit whether the needed resource algebra, language and adequacy theorem already exist. Do not begin by porting all of Rocq Iris or every time-credit logic.

**Additional source-bridge reference.** The October 2026 order-maintenance development [L14] supplies a concrete step-preserving translation to inspect, with its allocation and word-size assumptions. Rocq certifying extraction [R14] provides a different route from source functions to certified time bounds. Their existence does not provide an Aeneas adapter, but removes any justification for designing that bridge without studying these alternatives.

The final API may use one backend's semantics and Lean's `vcgen` as a front end. This is one connected stack only after the adapter theorem is proved. Two independently checked developments with similar vocabulary are not automatically interoperable.

## 8. Candidate module boundaries

Names below are provisional; adopt upstream namespaces where possible.

```text
ResourceBounds/Work/Occurrences       finite event algebra and exchange
ResourceBounds/Work/Charging          weighted bounded-fiber bounds
ResourceBounds/Contracts              backend adapter, not a new machine
ResourceBounds/Memo/Specification     independent body/cache contracts
ResourceBounds/Memo/Interpreter       chosen interpreter and soundness
ResourceBounds/Memo/Work              counts and representation costs
ResourceBounds/Batch                  preparation, job and repair accounting
ResourceBounds/Schedule               readiness and event accounting
ResourceBounds/Space                  occupancy and frontier bounds
ResourceBounds/Asymptotics            envelopes over Mathlib filters

SubtreeProofs/Complexity/Adapters/...  local source and representation bridges
SubtreeProofs/Complexity/Paper2004/... local theorem instances
SubtreeProofs/Complexity/DKM...        matching and schedule instances
```

Do not create all of these directories at campaign start. A module should first contain a coherent tested interface used by a client. Supporting lemmas should stay near their consumers until an independent reuse justifies extraction. Source-generation support belongs with the existing generation workflow.

## 9. Proof ergonomics acceptance

Measure an actual before/after client, not an aspirational line count. Record the number of manually repeated inductions, required representation unfoldings, duplicated arithmetic bounds, coercion boilerplate, imported modules and algorithm-specific lemmas. Keep a narrative explanation of the remaining hard argument. Shorter code that merely assumes the hard bound is a regression.

A client should be able to retain both an exact bound and an abstract envelope. The exact theorem is useful for representation review and small-input tests; the envelope is useful for callers. Changing a constant or a primitive implementation should usually alter the primitive contract and final envelope proof rather than every recursive invariant.

Automation comes after manually checked rules. Add only tactics that construct proofs from the established rules, report unsolved cost/size premises, and leave a readable theorem. Avoid automatic assumptions of constant-time operations, dropped failure branches or default-zero prices for unknown primitives.

## Sources

See [14-bibliography.md](14-bibliography.md), especially [L02--L06], [R01], [R05] and [I01--I04]. The proposed combined interface is campaign design, not a verbatim theorem from one paper.
