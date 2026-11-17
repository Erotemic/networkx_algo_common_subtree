# Independent edit-distance memo client, 2026-11-16

**Latest follow-up:** [actual-run work envelopes](memo-work-envelopes.md) now
prove primitive budgets and weighted bounds with setup for the declared C1
currencies. Unpriced input/body/key/materialization and source realization
remain open. The evidence below records the earlier milestone's scope.

The generic interpreter now has an unrelated client with an independently
specified optimum, two executable cache implementations, multi-root/warm-cache
contracts and checked request envelopes. This exercises W05 beyond the LV
recurrence. **Complete priced work envelopes remain open**, as do W04's other
interfaces and W06-C3. No quadratic Lean/Rust runtime or source refinement is
claimed.

## Independent specification

`Complexity/EditDistance/Specification.lean` imports no memo, tree or Rust
module. `Edits left right cost` describes head-consuming edit sequences:
insertion/deletion/replacement cost one and copying an equal symbol costs zero.
The empty sequence relates empty inputs at cost zero. This is the declared
edit model; its meaning is not defined by a memo evaluator's output.

`distance` is the separate, cache-free minimum-of-three recurrence.
`distance_le_edits` proves it is a lower bound on every valid sequence's cost;
`edits_distance` constructs valid edits attaining that cost. `distance_optimum`
combines the two directions. The implementation does not assume that matching
heads let it skip other recursive branches.

The upstream [AFP edit-distance example](memo-statement-audit.md#isabelle-reusable-memoization-correctness-stronger-preservation-needed)
informed the separation of edit semantics, index recurrence and memoization.
These are local checked Lean proofs, not imported Isabelle assumptions.
Limited pinned Std/Mathlib/Batteries searches found no `editDist`,
`editDistance` or Levenshtein declaration to instantiate. No global absence
or new-algorithm claim is made.

## Body, finite keys and reuse

`Complexity/EditDistance/Memo.lean` fixes the two input lists in the problem.
Keys are `Fin (left.length+1) × Fin (right.length+1)`, and the independent value
at `(i,j)` is `distance (left.drop i) (right.drop j)`. The body requests insertion,
deletion and diagonal states in that order, then returns the minimum; boundary
states return the remaining suffix length. A rank counts remaining input
lengths. `body_correct`, `requests_decrease` and `body_request_bound` are local
proofs; no global call/miss bound is a field.

`roots_spec` instantiates the **unchanged** generic `roots_envelope` theorem.
It supplies the finite index rectangle, local three-request bound, descent and
body correctness. The generic theorem then supplies actual-run success,
correct values, cache preservation, unique initially-absent expansion and
root-plus-body accounting. Its warm bound is

```
expansions <= initiallyAbsentIndexPairs.card
calls <= roots.length + 3 * initiallyAbsentIndexPairs.card.
```

Arbitrary root occurrences and sound warm caches are admitted. Input lists are
frozen; identical index dimensions do not justify cache reuse after changing
the input symbols. `initial_value_optimum` connects `(0,0)` to the independent
edit specification, including attainment and minimality. No tree/Rust proof
is imported by any edit-distance module.

## Concrete representations and cost boundary

`Complexity/EditDistance/Clients.lean` defines `runList` and `runDense` with the
same body, values, key type and generic combinatorial proof. Both expose setup
work separately from actual evaluation. `list_roots_spec` and `dense_roots_spec`
prove the same cold-cache rectangle envelopes from the same generic theorem;
only cache validity/soundness initialization is representation-specific.

`Complexity/Memo/ProductCache.lean` uses Mathlib's `finProdFinEquiv` rather than
an unchecked index map. Its actual expression is `column + width * row`.
The dense read/write counters each charge two arithmetic units for that
encoding plus one array-cell unit. In particular, key conversion is not silently
free in these operations. Array initialization creates every rectangle cell,
so its setup count is `(n+1)*(m+1)+1`; empty-list setup counts one.

These are **declared primitive currencies**. List lookup counts a whole-key
test. Dense encoding uses the bounded-word arithmetic model, not Nat bit cost.
Symbol comparison, input-list indexing/access, computing input lengths,
constructing bodies/keys, persistent array copying, materialization, arithmetic
width and source/allocator realization still need their own contracts. The
body's local five units count three score additions and two minima only.
Setup counters account for building the cache, not complete input conversion.
Thus the current client establishes independent correctness and combinatorial
reuse; it does not close MEM-03 or establish the classic total runtime bound.

## Validation

The 3,761-job main build, new edit-distance examples and 125-endpoint axiom
audit pass. Ten new endpoint closures use only the existing
`propext`, `Classical.choice`, `Quot.sound` baseline. New modules have no linter
warnings and no dependency pin or production/generated-source change.

`Tests/EditDistance.lean` checks empty inputs, insertion/deletion/replacement,
an independently constructed copy/replace/copy witness and its minimum cost,
multiple roots, empty roots, boundary-only setup and a stale cache from changed
inputs. Kernel-checked examples compare actual representations:

| One-symbol replacement | List | Dense |
| --- | ---: | ---: |
| Value | 1 | 1 |
| Calls / expansions | 4 / 4 | 4 / 4 |
| Lookup counter | 3 | 12 |
| Insertion counter | 4 | 12 |
| Body-local counter | 5 | 5 |
| Cache setup counter | 1 | 5 |

Small dense cases need not be cheaper; these are exact currency counts, not
performance measurements. Repeated roots add lookups without extra expansions.
An empty root list still pays the dense table setup. No native decision axiom
is used. The suite is registered in CI.

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/EditDistance.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

The next MEM-03 work is to prove representation primitive budgets along actual
runs and compose complete priced envelopes, including the retained local
input/body/key costs and finalization. The already checked LV bridge and this
client provide two consumers; they do not waive the source/RAM/heap obligations
or the campaign's independent-review gate.
