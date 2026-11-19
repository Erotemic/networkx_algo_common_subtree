# Choice owner ledgers and a constructive original-loan call

Baseline: `f8c29e2` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [combined parent witness/query bounds](memo-evaluator-retained-right-provenance.md)
are available at the actual `finishCode 6` checkpoint. This increment supplies a
generic forward choice constructor and its derived output provenance. It does
not yet assemble either actual parent choice instruction and its temporary setup.

## Primitive control and invocation ledgers

`SourceNoCallOwnerLedger.lean` reuses the existing
`Derived.action_owner_subset` from `SourceClosedMachine.lean`. Derived scrutinee
execution preserves the active owner permutation. `Flow.OwnerSubset` includes
both the returned packet inventory and the remaining activation inventory.
`Calling.exec_noCalls_owner_subset` composes the actual ledger through primitive
instructions, continuation-aware reference preparation, selected switch arms,
early returns and remaining continuations. Complete input resources and actual
successful execution are explicit; the theorem supplies no physical progress
assumption disguised as an input ownership specification.

`SourceNoCallInvokeOwnerLedger.lean` carries this subset through actual parsed
entry, return extraction and checked stack closure. Initial owner inventory is
identified with the actual input packet footprint. Closure preserves packet
memory. Both invocation and guarded invocation return an actual output footprint
whose owners are a subset of the input owners. Caller/external owners remain
outside this selected subset.

## Actual recursive choice and caller storage

`Recursive.original_choice_owner_ledger` specializes the generic invocation
ledger to the real parsed choice body, whose no-call property is checked against
the pinned declaration. `Derived.choice_call_owner_provenance` reflects the
actual caller operands, partitions complete owner resources into transferred
input and suspended context, applies the callee subset ledger, and carries the
exact packet owners through guarded destination storage. Bounds on the actual
moved input owners therefore bound the selected stored witness. No freshness
claim treats the callee's output descendants as newly allocated by choice.

These are successful-call transfer theorems. They do not by themselves construct
either parent call or assume successful whole-parent evaluation.

## Constructive original-loan choice call

`OriginalLoanMachine.arguments_loans_of_fresh` derives transfer permission from
input owner bounds. Actual argument footprints bound transferred owners at or
above the original incoming heap; the maintained loan family and actual old
caller inventories bound suspended loans strictly below it. The proof permits
unrelated query/table/caller aliases and needs no universal alias ban.

`Recursive.original_choice_callee_same` uses the actual choice body's no-call
property to identify executions across every positive recursive fuel and any
helper budgets. It does not change the existing dispatcher or its fuel rules.

`Evaluator.original_choice_complete` constructs argument moves, actual parsed
choice entry/body/closure and guarded result storage from two initialized native
witnesses in an original-loan machine. Its forward premises include their
independently derived owner bounds, distinct local slots, existing bounded loan
family, and a fresh empty destination root. It derives the selected native value,
complete exact call cost, original-loan machine, output owner bound, exact
root/count/frame and untouched root bytes. Bounded untouched locals retain their
owner inventories. The same constructed final world/activation and exact cost
work at every positive fuel and any helper budget.

No successful choice call, expected final machine or desired post-frame is
supplied to this forward constructor. Earlier APIs, native contracts,
independent specifications, maintained Rust, generated output and actual source
semantics are unchanged.

## Consumers

The strengthened arbitrary-score consumer in `Tests/SourceAddressedControl.lean`
constructs the complete real choice invocation for a nonempty first witness and
an empty second witness, at arbitrary helper fuel/budget. Its actual output
footprint is a subset of the original two-owner input inventory. All score pairs
are quantified, covering both winning branches and ties, including retention or
destruction of the first witness's two Boxes.

The parent-call consumer now uses `original_choice_complete`. A complete closed
input machine and two input bounds construct the actual recursive choice call
with exact selected native value/cost and complete output ownership. No run or
post-frame is supplied. Its quantified positive recursive fuel and arbitrary
helper budget consume the stable constructor directly.

## Validation and reproduction

The root library builds in 4,270 jobs. The complete affected addressed-control
suite passes. All 1,989 unique audited endpoints, including ten new public
theorems across four new modules, retain only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds resolve 1,081 unique declarations
with zero unknown references.

The complete parent suite at `f8c29e2`, seven Lean suites/eight runtime cases,
thirteen Rust tests and nine Python checks at `2db7171`, and full 47-suite/native-WP
evidence at `d49f638` are inherited, not rerun for this proof-only extension.
All seven build caches remain guest-ext4 bind mounts; no Rust build runs here.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-choice-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_choice_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.OriginalLoanMachine.arguments_loans_of_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_choice_callee_same \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_noCalls_owner_subset \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.invoke_noCalls_owner_ledger \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.guardedInvoke_noCalls_owner_ledger \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_choice_owner_ledger \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.choice_call_owner_provenance
```

Machine-local evidence uses `/var/tmp/subtree-choice-provenance-{ledger,invoke,
call,original,build,consumer,axioms,statements}.log` and statement JSON. Shared
source scanning supplies candidates; kernel acceptance, axiom auditing and
elaborated statement closure establish endpoints and assumptions.

## Remaining work

At the existing parent checkpoint, construct actual temporaries 99--102 and the
first choice from 101/102 into 100; retire its moved arguments, transfer right
witness 95 through 103 and construct the second choice from 100/103 into 99.
Retain selected-witness and both owned-query bounds through complete source
cleanup, then construct insertion, output assembly and remaining owned cleanup.
The generic forward choice constructor is complete; this parent sequence is not.

Complete both optional joins, overflow/failure paths, remaining parent returns
and general pair/pair induction, including the universal `NativeTotalFresh`
contract. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and all other planning requirements remain
open. No SRC-01/C3 or production resource closure is claimed; the full goal is
active.
