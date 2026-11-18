# Retained witness and owned-query provenance through the complete right region

Baseline: `683b06a` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [complete left witness/candidate/query bounds](memo-evaluator-left-witness-provenance.md)
now cross right-query construction, the actual right recursive call and all its
cleanup. At the successful-right payload checkpoint all three candidate witness
bounds and both owned contraction-query bounds are available together.

## Constructed right-query prefix

`pair_right_concat_call_complete_provenance` derives the owned right word's
bound from the actual concatenation helper ledger. Actual call-preservation and
primitive cleanup retain all three incoming bounds: candidate 64, left query 71
and held left witness 81. The helper's native arguments and readiness are derived
from the constructed argument scope; no expected successful parent invocation
or desired post-frame is supplied.

`pair_right_concat_scope_complete_provenance` composes the five preceding actual
argument instructions. `pair_right_prefix_complete_provenance` includes all six
successful-left payload instructions and all nine right-concatenation steps.
Its output has independently established owner bounds for 64/71/81/85.
`entry_pair_right_prefix_complete_provenance` retains every earlier parsed-entry
checkpoint, the actual left call and cost, native successful-left discriminant,
full matched/left prefix, exact native right concatenation events/cost and all
future unbound roots at index 88 or above.

## Complete actual right recursion

`pair_right_scope_complete_provenance` independently reconstructs the actual
right arguments and identifies them by prefix determinism. Both query snapshots
and the transferred native table establish readiness for the real right call.
The explicit smaller `NativeTotalFresh` contract derives right tuple-witness
provenance; the old table owners remain unrestricted. Actual argument moves,
call execution/storage and all eleven result cleanup steps retain the four
existing bounds. Optional right witness 88 receives its own derived bound.

`pair_right_from_concat_complete_provenance` composes actual original/fresh
right views with the complete call/result scope. The fresh right-word anchor is
separate from the strictly original query/table/caller loan family.
`entry_pair_right_scope_complete_provenance` retains all seventeen earlier stable
parsed-entry prefix boundaries, both actual contraction calls and exact complete
costs, full matched/left and right action prefixes, exact native optional/table
outputs and all future roots at index 96 or above. It returns the right witness
bound at 88 together with all four retained bounds at 64/71/81/85.

## Actual successful-right payload continuation

`pair_finish_payload_complete_provenance` extends the existing unchanged payload
constructor by carrying the four held bounds through all six real instructions.
The right witness moves from 88 through scratch 96 into 95, and the moved scratch
is physically retired. The resulting `finishCode 6` checkpoint has bounds for
all three candidates 64/81/95 and both owned queries 71/85.
`FinishPayloadScope` continues to record child-view masks 27--30 as logically
ended, with their physical roots awaiting later cleanup.

All bounds are relative to the original parent heap. Smaller head/tail/left/right
`NativeTotalFresh` contracts and independent native success/checked-add equations
remain explicit. Earlier endpoints, both native contract definitions, maintained
Rust, generated files, independent specifications and source semantics are
unchanged. This does not construct either choice or establish the universal
stronger recursive contract.

## Combined nonempty consumer

The added `Tests/SourceCacheMissSetup.lean` consumer starts with twenty old table
Box owners and queries borrowing a nonempty table-owned word. All four child
requests hit nonempty cached Pair witnesses of score seven. Proved empty-query
fresh contracts discharge all smaller requests. Actual parsed entry, both
contraction calls, all result cleanup and six successful-right payload steps
yield three real owner inventories simultaneously: six owners at candidate 64,
two at held left witness 81 and two at held right witness 95. Every listed owner
is at or above the incoming parent heap length. Both query bounds remain.
Neither cache soundness nor successful whole-parent execution is supplied.

## Validation and reproduction

The root library builds in 4,266 jobs. The complete affected parent consumer
suite passes. All 1,979 unique audited endpoints, including eight new public
theorems across seven new modules, retain only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds resolve 1,317 unique declarations
with zero unknown references.

The seven-suite/eight-runtime-case, thirteen Rust test and nine Python check
evidence at `2db7171` is inherited, not rerun for this proof-only extension.
The full 47-suite/native-WP evidence at `d49f638` is also inherited. All seven
build caches remain guest-ext4 bind mounts; no Rust build runs in this increment.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-right-held-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_scope_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_payload_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_scope_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_from_concat_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_prefix_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_prefix_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_concat_scope_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_concat_call_complete_provenance
```

Machine-local evidence uses `/var/tmp/subtree-right-held-provenance-{prefix,
entry,finish,build,consumer,axioms,statements}.log` and the corresponding statement
JSON. Shared source scanning supplies candidate names; kernel acceptance,
axiom closure and elaborated statements establish endpoints and assumptions.

## Remaining work

Use these combined bounds to construct both actual chooseLonger calls, insertion,
output assembly and later selected owned cleanup. Complete both optional joins,
overflow/failure paths, remaining parent returns and general pair/pair induction,
including the universal `NativeTotalFresh` contract. Dynamic regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and all
other planning requirements remain open. No SRC-01/C3 or production resource
closure is claimed; the full goal is active.
