# Head/tail witness provenance through the actual matched candidate

Baseline: `2569452` on `Droschinsky-algos`. Targets: SRC-01 / W06-C3.
This extends the [right-child/payload endpoint](memo-evaluator-right-payload-provenance.md)
with a separate constructive bound for the matched candidate at its construction
checkpoint. It does not yet combine all three candidate bounds at either choice.

## Checked calls and primitive transfers

`SourceCallOwnerProvenance.lean` proves `Derived.call_keeps_owner_provenance`
from the actual call, reflected operands, readiness, and the existing source
mutation certificate. The canonical local inventory survives operand evaluation,
callee execution and guarded result storage. The helper variant
`helper_call_owner_provenance` uses the existing allocation ledger to bound both
transferred input owners and freshly allocated owners. Its recursive-dispatch
variant `original_helper_call_owner_provenance` also checks positive fuel and
that the selected function is a helper.

This covers `boxNew`: the new outer shell lies beyond this helper's incoming
heap, while its payload can contain previously allocated owners. Those payload
owners keep their independently established bound relative to the original
parent heap. No claim makes all payload descendants newly allocated by boxNew.
Insertion and boxNew remain outside the older fresh-output helper class.

`SourceCheckedAddOwnerProvenance.lean` reconstructs scalar readiness from an
actual successful checked-add call, readable packets and the concrete helper's
width checks. `Prefix.checkedAdd_keeps_owner_provenance` propagates a bound
through actual scalar-call prefixes and their continuation preparation. Numeric
overflow is an ordinary optional result and does not invalidate preservation.
This does not prove the evaluator's complete overflow exit.

`SourceAggregateOwnerProvenance.lean` combines bounds from both moved operands
of an actual aggregate assignment, then carries the destination bound through
primitive cleanup. The existing generic optional-payload theorem moves to
`SourceOptionalPayloadOwnerProvenance.lean` with its namespace, statement and
proof unchanged. The right-payload module imports it; it is not a new endpoint.

## Constructed head, tail and scoring scopes

`pair_head_scope_complete_fresh` and `pair_tail_scope_complete_fresh` construct
the earlier full 26- and 24-instruction regions using the explicit smaller
`NativeTotalFresh` contracts. They derive the optional head bound at 31, retain
the extracted head at 37 across the actual tail call, and derive the optional
tail bound at 41. The owned memo-table field remains unrestricted.
`entry_pair_head_scope_complete_fresh` and
`entry_pair_tail_scope_complete_fresh` compose these with real parsed entry and
retain all earlier stable prefix checkpoints and native result discriminants.

`score_tail_payload_complete_fresh` transfers the actual successful tail payload
through scratch 48 into 47 while preserving head 37. The score/root-score scope
and parsed-entry variants retain both initialized witness bounds across the
actual fifteen subtotal instructions and twelve root-score instructions. Their
old count/frame/root/heap guarantees, native checked-add results and discriminant
inspection remain available. Independent native head/tail successes and subtotal
success still select later paths; a root-score result may overflow.

## Actual matched construction

`original_boxed_word_complete_fresh` preserves the old forward constructor's
complete guarantees and adds a derived output bound plus preservation for every
bounded, untouched local. The first three real instructions transfer the source
word into temporary storage; the real box helper transfers those bounded owners
and creates its new shell; physical temporary retirement retains the result.

`pair_matched_boxes_complete_fresh` constructs both Boxes at 66/68 and preserves
the first inventory across the second call. The word/embedding variants move
these owners into 65 and then combine the word with a scalar score into 64.
`pair_matched_scope_complete_fresh` composes all thirty construction instructions.
`entry_pair_matched_scope_complete_fresh` retains seven stable prefix checkpoints
from parsed evaluator entry, complete ownership/coverage, exact native matched
value, count 113, retired construction roots and unbound concatenation storage.
It derives `LocalOwnersAbove world.memory.length final after 64`.

The only stronger recursive premises here are smaller head/tail
`NativeTotalFresh` contracts. Independent native success and checked-add equations
remain explicit. No desired physical post-frame, cache-soundness assumption,
successful whole-parent invocation or universal stronger recursive contract is
supplied. Existing endpoint statements and both native contract definitions are
unchanged.

## Nonempty parent consumer

The added consumer in `Tests/SourceCacheMissSetup.lean` starts with twenty old
table Box owners and original queries borrowing a nonempty table-owned word.
Both child requests hit nonempty cached Pair witnesses of score seven. Proved
empty-query fresh contracts discharge the smaller recursive premises; independent
native equations establish scores fourteen and fifteen. Parsed entry, both
calls, score work, allocations and aggregate cleanup yield an actual inventory
at 64 with exactly six bounded Box owners. Construction temporaries 65--70 are
physically unbound. No cache-soundness premise forbids the deliberately oversized
cached witnesses.

## Validation and reproduction

The 4,251-job root build and seven affected Lean suites pass, including the new
nonempty consumer and all eight recursive runtime cases. All 1,963 unique audited
endpoints retain only `propext`, `Classical.choice` and `Quot.sound`. This adds
22 public theorems in eighteen modules, one of which relocates the existing
optional-payload theorem. Eight elaborated statement seeds resolve 1,320 unique
declarations with zero unknown references. Thirteen ordered Rust tests and nine
Python frontend checks pass. Full 47-suite/native-WP evidence at `d49f638` is
inherited, not rerun.

Maintained Rust, generated output, independent specifications, source semantics,
dependency pins and shared tooling are unchanged. All seven build caches are
guest-ext4 bind mounts. Cargo metadata selects the mounted standalone target;
Cargo/Rustup homes are ext4.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceOwnerProvenance.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-candidate-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_matched_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_tail_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_score_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_score_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_boxed_word_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.original_helper_call_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.aggregate_two_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.checkedAdd_keeps_owner_provenance
```

Machine-local logs use `/var/tmp/subtree-candidate-provenance-`: `build`,
`consumer`, six corresponding `Source*.log` suite names, `axioms`, `statements`,
`rust` and `python`. Shared source scanning supplies candidate names; the kernel
audit and elaborated statement queries establish checked endpoints/assumptions.

## Remaining work

Carry the candidate bound from construction through both contraction calls to
the final choices. Derive the left recursive witness bound and transfer it to
81; retain both concatenated-word bounds at later parent checkpoints. Combine
these with the earlier right witness bound at 95, construct both actual
chooseLonger calls, insertion, output assembly and later selected owned cleanup.
Complete both optional joins, overflow/failure paths, remaining parent returns
and the general pair/pair induction, including `NativeTotalFresh`.

Dynamic parsed regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning requirement remain
open. This increment does not complete SRC-01/C3, establish a production resource
bound or finish the full user goal.
