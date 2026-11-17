# Stable typed lookup shared loans: 2026-11-17

Baseline: `fde08d2`. This advances W06-C3 from
[normal storage discipline](lookup-stack-storage.md) to dynamic immutable
shared-loan validity throughout the actual lookup helpers. Every shared value
is backed by a typed read in the retained caller heap; source-created reborrows
preserve that origin. Ordinary results contain no shared references, including
inside owned payloads. This is not source region binding/outlives adequacy.

## Actual reads and address origin

`Rust/LookupBorrowLoans.lean` defines `Loan base pointer ty` using an actual
read and independent `Heap.Typed` witness in the earlier caller memory.
`Loan.root_bound` proves the address predates new allocations. `Loan.stable`
preserves the same typed target under every memory extension.

`Safe base current cell ty` tracks these loans recursively through aggregates
and current owned payloads. Its shared constructor carries a loan in `base`;
fresh owned cells are allowed in `current`. `Safe.typed` additionally requires
`Extends base current`, which is essential: an old read alone does not justify
a read in mutated/freed memory. `EnvSafe` covers every occupied local, and
`FieldsSafe` covers the complete temporary argument list. Their extension,
clear and store lemmas preserve these witnesses. Typed input values in the
initial heap construct the initial loan invariant.

`Rust/LookupBorrowPlaces.lean` proves a stronger address-origin result than
current typing alone. Crossing a typed shared reference gives an actual view
in the retained heap. Subsequent field projections and owned dereferences
preserve that old view, with actual pointer reads proved at each stage.
`borrow_safe` constructs the resulting loan from those reads.

The executable `fromShared` route check requires a source-created borrow to
reach its referent through a shared pointer. A fresh owned local cannot acquire
an earlier-heap origin merely because it is well typed. This is a stronger
property of these four actual helpers, not a claim that every Rust-valid borrow
must satisfy this route rule. Native lookup's full represented-input domain is
preserved: its initial typed shared arguments establish the invariant with
the initial memory as `base`.

## Source checks, primitives and recursive traces

`Rust/LookupBorrowCertificate.lean` reads the complete retained JSON through
the existing typed source reader, checks exact normalized bodies and checks
every borrow route against the actual declared local types. Its soundness
theorem exports body constraints, argument/return prefixes and route witnesses
for every ordinary helper, using explicit helper coverage. Original and actual
extra-comparison mutant both pass `decide +kernel`. The JSON, declarations and
dependency pins are unchanged; no native proof oracle is used.

`Rust/LookupBorrowPrimitives.lean` proves preservation through actual invalidating
moves, copies, sequential operand lists, aggregate construction and scrutinees.
Reborrows use the address-origin proof. Borrowing does not take ownership or
mutate the referent; shared aliases remain supported.

`Rust/LookupBorrowExecution.lean` records the actual loan-safe environments and
post-operand temporary bundles at statement/control frontiers. Every frontier
retains `Extends base current`. `Trace.erases` recovers the unchanged complete
execution/cost; `exec_safe` constructs the trace and safe result. A local
callee contract is subsequently discharged, not assumed as a final property.

`Rust/LookupBorrowCalls.lean` discharges it by fuel induction with the same
retained base across all nested calls. Ordinary calls use checked prefixes,
types and routes; generic Box transfers its safe payload into the actual fresh
cell. `original_safe` and `mutant_safe` cover every function/fuel on safe typed
arguments and preserve old memory. Caller loans remain valid throughout these
traces, including while caller locals are suspended or their pointer slots
are subsequently cleared.

## Results and public composition

`Rust/LookupBorrowOutputs.lean` defines `Unborrowed` over the complete returned
value, recursively following actual owned heap cells. `typed_unborrowed`
derives it from independent constructor signatures and closed output types.
All four ordinary helper output types are closed. This excludes a shared
reference hidden inside an owned Box, as well as a shared top-level result.
Generic Box remains able to carry an existing loan; it is explicitly excluded
from the ordinary-output type lemma.

`Rust/LookupBorrowRefinement.lean` composes both retained source-control programs
with actual addressed runs, recursive loan traces, independent readback and
the same full costs/allocation growth. `lookup_loan_total` constructs successful
native-input lookup at sufficient fuel with loan-safe, borrow-free output;
stack/spatial/frame certificates; exclusive returned ownership; independent
typed first-hit readback; and exact existing events/allocation bounds. Every
valid external owner frame is retained, and every pre-existing typed loan
still reads its typed target afterward. Actual existence comes from the
previous native totality theorem, not from checker acceptance alone.

## Validation

The main 3,815-job build, all fifteen Lean suites, native WP example, seven
Python frontend tests and 382-endpoint axiom audit pass. Forty-four new audited
closures stay within `propext`, `Classical.choice`, `Quot.sound`; new modules
have no warnings. Rust, generated code/JSON, main pins and extraction tooling
are unchanged; prior pinned regeneration remains the provenance baseline.
Shared `leanq` inspected `lookup_loan_total`'s elaborated statement closure
(438 records), including its unchanged native-input premises, actual run,
loan/storage/spatial/frame witnesses, borrow-free result and retained frames.

`Tests/LookupBorrow.lean` is in Lean CI. A currently typed pointer into a new
allocation has no loan in the older heap. A type-correct fresh-root borrow
fragment fails the stronger old-root route profile, without being claimed
Rust-invalid. Other cases cover stable reads after allocation, clearing the
local shared-pointer slot, mutation/freeing failing the extension premise,
and a well-typed owned Box containing a valid shared loan that nevertheless
fails `Unborrowed`. Actual lookup's result theorem is exercised with aliased
queries. These are explicit model inputs/fragments, not new compiled Rust
mutations. Both actual retained programs pass their complete kernel certificates.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupBorrow.lean)
(cd proofs && lake env lean Tests/LookupStack.lean)
(cd proofs && lake env lean Tests/LookupSpatial.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Optional elaborated statement inspection through the shared tools.
leanq --project proofs statement SubtreeProofs.Rust.LookupSource.Heap.Borrow.lookup_loan_total \
  --root-module SubtreeProofs.Rust.LookupBorrowRefinement
```

## Remaining source obligations

Dynamic typed shared-loan validity and non-escaping ordinary results are now
proved in the immutable interpreted lookup fragment. The retained source's
region identities are still erased by the type reader. Their binding, outlives
relations and correspondence to the official typed LLBC/Rust interpretation
remain open. This does not establish full borrow-checker correctness, physical
stack/provenance semantics, mutable loans, freeing or failed/unwind behavior.

Next connect the checked interpretation and region erasure to source adequacy,
then extend to insertion, concatenation, memo evaluation/core and wrappers.
Keep remaining local/source costs and physical space/runtime obligations
separate from this exact declared-currency result. W06-C3, SRC-01, MEM-04 and
the full planning objective remain open.
