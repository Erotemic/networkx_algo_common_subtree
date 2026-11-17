# Exclusive returned lookup ownership: 2026-11-16

Baseline: `685a12f`. This advances W06-C3's ownership obligation for the
[addressed lookup realization](lookup-heap-realization.md). It proves unique
returned Box ownership and complete fresh-allocation readback. Intermediate
local reset/destruction and official typed source/lifetime simulation remain
required. Final-state ownership does not imply those trace properties.

## Independent ownership and occurrence accounting

`Rust/LookupHeapOwnership.lean` defines `Owns memory cell start stop` and
`OwnsFields`. They allocate adjacent postorder intervals to aggregate fields.
An owned Box has a payload interval followed by its cell at that interval's
end. Scalars and shared references own an empty interval. Shared aliases remain
permitted; this is ownership of Box occurrences, not a ban on shared read paths.
Heap-extension lemmas preserve these ownership facts.

The independent `Footprint`/`FieldsFootprint` relations enumerate **all owned
occurrences**, traversing owned pointees and concatenating their lists. They
do not discard duplicates by constructing a set. `Footprint.unique` proves
this traversal has a unique result for a given value/memory. Inversion lemmas
let its mutual proof recurse directly on finite footprint evidence.

`Owns.footprint` connects the interval judgment to exactly
`List.range' start (stop - start)`. `Owns.exclusive` proves that **every**
footprint equals this range, is duplicate-free, and has membership precisely
`start ≤ address ∧ address < stop`. Thus duplicated owned aliases, old-cell
reuse and omitted cells cannot satisfy a fresh complete region judgment.
`alloc_owns`, `packWord_owns` and `packResult_owns` construct these judgments
for the actual postorder allocation layouts.

## Direct connection to generated execution

`Rust/LookupHeapLayout.lean` proves exact returned value **and final heap**
layouts for the existing addressed interpretation of the generated normalized
program. This strengthens the previous snapshot representation result, which
by itself permits aliased Box pointers.

- `Layout.copy_layout` structurally follows the generated `copy_word` body.
  For arbitrary represented shared input pointers, its returned cell/heap
  equal `packWord word memory`. It unfolds the actual generated control and
  primitive execution, preserving reads across the first recursive allocation
  before copying the second child.
- `Layout.copyResult_layout` proves the corresponding exact `packResult`
  layout for the generated result-copy body, including the unchanged scalar.
- `Layout.lookup_layout` follows the actual generated lookup body. Existing
  comparison contracts leave memory unchanged; misses recurse into the actual
  suffix; the first hit uses the proved result-copy layout. Its output is
  `outputLayout (LookupEvents.lookup table left right).1 memory`.
  `LookupEvents.lookup_value` identifies this option with independent
  `findResult`. No sound-cache or unique-key hypothesis is introduced.
- `Layout.outputLayout_owns` gives the complete fresh ownership region for
  that layout, including empty ownership and unchanged memory for `None`.

These results retain the established sufficient-fuel hypotheses. They do not
replace execution by a layout constructor: successful execution of the actual
generated instruction body is proved to produce that layout. Input pointers may
alias. The complete cost is still the actual interpreter result; the earlier
cost-preservation/first-hit theorems remain unchanged.

## Public ownership contracts

`Rust/LookupHeapReturnOwnership.lean` identifies each completed sufficient-fuel
run with its exact layout and exports:

- `copy_return_owns` and `copyResult_return_owns`;
- `lookup_return_owns`;
- `lookup_return_footprint`: an occurrence list that is duplicate-free, covers
  exactly all addresses from the initial to final heap length, and whose length
  equals the actual `cost.events.allocations`; existing memory is preserved;
- `lookup_no_old_owned_alias`: no address below the initial heap length occurs
  as an owned Box in the output, for any output footprint proof.

Together with the earlier typed first-hit readback, lookup returns a deep fresh
owned witness, rather than merely the right immutable tree value. Every newly
allocated logical Box is accounted for exactly once in that returned witness.
No condition on unreachable old warm memory is added. These are conclusions
about the explicit addressed interpreter, connected to the retained source
control certificates; official source-primitive adequacy remains separate.

## Checks and adversaries

The 3,779-job build, all nine Lean suites, native WP example, seven Python
reifier tests and 190-endpoint audit pass. All fifteen new audited closures
stay within `propext`, `Classical.choice`, `Quot.sound`; new modules have no
warnings. See [`PROOF_STATUS.md`](../../../../proofs/PROOF_STATUS.md). The existing
`Tests/LookupHeap.lean` suite now includes a value with two owned fields pointing
to the same Box. It has valid independent typing and snapshot representation,
but its footprint is `[0, 0]`, so exclusive ownership is impossible. Further
kernel-checked examples reject an old input Box as fresh output and a new
allocation missing from the returned footprint. These are explicit semantic
countermodels, not additional compiled Rust mutations. The existing real
extra-comparison mutation and its cost tests remain unchanged.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupHeap.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Main pins, Rust, generated code/JSON and extraction tooling are unchanged.
The prior full pinned regeneration remains the source-provenance baseline.
No new native proof oracle, admission or axiom is introduced.

## Remaining obligations

Returned exclusive ownership and absence of lost **final** allocations are now
proved. An invariant over every intermediate frame must still justify safe
resets/overwrites, local moves, all callee argument ownership and conditional
destruction. The current heap interpreter does not free cells. It does not yet
certify those intermediate operations merely because their final result is
exclusive. Stack borrows/lifetimes, mutable storage, checked retained-JSON field
signatures and official typed LLBC/Rust simulation remain open.

Insertion, concatenation, memo evaluation and a named core/wrapper still need
the extended source/heap contracts. Logical Box allocation volume/returned
ownership is not physical peak space, allocator bytes/work or CPU runtime.
SRC-01, MEM-04, APP-01 and the complete planning objective remain active.
