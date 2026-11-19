# Addressed memo primitive layouts and owner transfer: 2026-11-17

Baseline: `63f929f`. Six `Rust/MemoHeap*.lean` modules extend the
[actual concatenation/insertion source bridge](memo-source-primitives.md) to
addressed execution, independently typed output readback, exact allocation
growth, fresh concatenation ownership and transfer of insertion's owned table.
The new complete ownership ledger preserves every old occurrence and adds each
new Box exactly once. Intermediate static typing, local guard/storage/spatial
traces and loan/region certificates for these new functions remain open.

## Shared addressed execution

`LookupHeapExecution` now supports arbitrary callee-target types in addressed
instruction/control execution, borrow-route checks, local callee simulation
and the action/statement simulation theorems. The original `Calls` alias and
lookup call driver retain their original specialization. Two call-free test
fragments now supply an explicit lookup callee type to disambiguate the generic
API; their assertions are unchanged.

`MemoHeapExecution.run` supplies the memo function entry and fresh Box behavior
to that same instruction engine. `run_spec` discharges the local callee
simulation by fuel induction, including actual allocation. Every successful
source-model call on represented arguments has a successful addressed call
with exactly the same complete cost, represented result, immutable old-memory
extension and `after.length = before.length + cost.events.allocations`.
`program_borrows` checks every actual body; borrowing a local stack slot is
still rejected. `certified_run_spec` composes this with the retained source
program and its kernel-checked normalization. This is a forward successful-run
simulation, not a claim of failure equivalence with arbitrary heap executions.

Input/output typing comes from independent `Heap.Shape`, represented native
values and the already proved snapshot typing. It does not yet establish
operational type preservation at intermediate local states from these new
source annotations. No source declaration, Rust, generated artifact or pin is
changed in this increment.

## Actual output layouts

`MemoHeapLayout` proves exact fresh postorder layouts for the actual copy-word,
copy-result and concatenation bodies. The copy proofs follow actual pointer
reads and field/owned dereferences, including old-memory stability across
allocation. Concatenation's output and final heap are exactly
`packWord (appendWord left right) before`. This independently constructed
layout allocates each output Box once; all its owned addresses are fresh.
The equality concerns the actual execution, not merely a final snapshot value.

`MemoHeapInsertion` uses a different layout. `packInsert` copies the two keys
and supplied witness into `packEntry`, allocates its entry Box, then allocates a
tail Box containing the **original input table cell**. The output is the table
constructor with those entry/tail Boxes. `insert_layout` proves the actual
source body has this exact output and heap. It does not copy the old table.
`packInsert_tail` additionally identifies the output field and its actual
memory read, rather than concluding table identity from representation alone.

Both layouts use the complete charged instruction execution, including
invalidating local moves and rejecting live owned drops. The final ownership
proof does not infer intermediate cleanup or local storage discipline from
returned reachability.

## Exclusive owners and the retained table

`MemoHeapOwnership.packEntry_owns` and `entryLayout_owns` establish the fresh
copied-entry interval. The reusable `Spatial.fresh_owns` combines a fresh owned
interval with an arbitrary earlier separated owner frame. `packInsert_frame`
then transfers the original table under its new tail Box and packages the two
output fields, preserving every external owner frame.

The whole inserted result cannot be described by lookup's fresh-only ownership
interval: it legitimately includes old table Boxes. `packInsert_footprint`
retains a complete ordered occurrence list: fresh copied entry, original table
occurrences, then the fresh tail Box. `packInsert_ledger` proves this list is a
permutation of the old table list followed by the complete fresh allocation
range. Multiplicities are preserved; replacing the list with a set would lose
the duplicate-owner obligation.

`MemoHeapRefinement.insert_return_ledger` connects this to actual execution:
its length is `old.length + cost.events.allocations`, and a duplicate-free old
list yields a duplicate-free returned list. `insert_return_frame` preserves
all external owner frames provided the input table and that frame were
separated. Shared query/witness pointers may alias each other or refer into the
owned table being transferred. An aliased old owned footprint cannot acquire
exclusive ownership merely because insertion adds fresh cells.

## Native totality, resources and nonvacuity

`concatenate_total` and `insert_total` retain actual certified source execution
and addressed execution with the same cost; independent typed append/prepend
readback; native translated-Rust agreement; old-memory extension; exact Box
allocation growth; unchanged structural operation events; and returned owner/
frame guarantees. Concatenation owns the complete fresh interval. Insertion
retains the original table cell at its fresh tail address and preserves the
input table's owner frame. No sound-cache, unique-key, optimal-witness or
consistent-score premise is introduced.

The preceding exact event theorems now count actual addressed heap cells:
concatenation adds exactly `2*(L+R)` cells; insertion adds exactly
`2*(L+R+W)+2`, where `L`, `R`, `W` are key/result word semilengths. The full source
instruction count remains in the same `Cost.steps`; no final instruction
pricing envelope or physical allocator/byte/space theorem is claimed here.

`MemoHeapInputs` constructs represented shared inputs for every native word/
witness and a duplicate-free owned table layout for every native table.
`insert_inputs_exist` also preserves all earlier external owner frames.
These inhabit the public premises without assuming the desired output property.
They are input materialization outside the primitive contracts, not uncharged
setup inside them.

## Validation and reproduction

The main 3,835-job build, all eighteen Lean suites, native WP example, nine
Python reifier tests and 461-endpoint axiom audit pass. All 31 new audited
closures stay within the accepted `propext`, `Classical.choice`, `Quot.sound`
baseline. New modules have no warnings. Rust, generated inputs/programs, source
readers, dependencies and extraction pins are unchanged. The preceding
`63f929f` full pinned regeneration and thirteen ordered Rust tests remain the
provenance/behavior baseline; there is no new Rust regeneration in this proof
increment. Shared `leanq` inspected the elaborated statements and dependencies
of `insert_total`, `insert_return_ledger` and `concatenate_total` (597 records),
confirming actual source/heap success, independent readback/costs, conditional
frame preservation and multiplicity-retaining ownership statements.

`Tests/MemoHeap.lean` is in CI. Actual insertion is exercised with both keys
aliasing a field of the owned input table and the witness also borrowed from
that table. A distinct external owned cell survives; the returned ledger is
`[3, 0, 1, 4]`, and a wholly fresh ownership interval is rejected. A separate
proof fragment shows insertion cannot repair a duplicated old ownership list.
Nonempty concatenation accepts identical input pointers and returns complete
fresh output. Dangling key reads fail explicitly. Constructive input existence
covers arbitrary native tables, words, witnesses and earlier memories.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/MemoHeap.lean)
(cd proofs && lake env lean Tests/LookupHeap.lean)
(cd proofs && lake env lean Tests/LookupTypePreservation.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement SubtreeProofs.Rust.MemoSource.Heap.insert_total \
  SubtreeProofs.Rust.MemoSource.Heap.insert_return_ledger \
  SubtreeProofs.Rust.MemoSource.Heap.concatenate_total \
  --root-module SubtreeProofs.Rust.MemoHeapRefinement
```

## Next required work

Retain these addressed/layout/returned-owner endpoints. Next check the new
source declarations, static constraints and regions, and connect them to
intermediate operational typing, guarded local/storage/spatial traces and
shared loans. Insertion's argument profile includes an owned table; do not
reuse lookup's all-shared profile or fresh-only return theorem unchanged.

Then handle the actual memo evaluator's owned-local borrows, checked arithmetic,
losing-candidate destruction and overflow/table returns, and compose one public
core. Indexed/token/reconstruction wrappers, normal work/input/error policy and
G3 adversaries remain required. The model still has immutable heap extension,
no physical stack/provenance or general free/mutation/unwind semantics, and an
explicit Charon/source-primitive/compiler/runtime boundary. W06-C3, SRC-01,
MEM-04, APP-01 and the full planning goal remain open.
