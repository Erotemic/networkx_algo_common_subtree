# Constructed recursive helper and choice calls

Date: 2026-11-18. Baseline: `17180e7` on `Droschinsky-algos`. Six proof
modules add 18 public checked theorems. Choice now executes through the actual
recursive dispatcher with one unit of fuel. Whole helper and choice call steps
construct one-pass argument extraction, their actual callee, and checked result
storage from independent local source steps, types, ownership and loan facts.
No successful parent/callee call, expected final heap, post-argument owner ledger
or post-callee frame is supplied to these totality endpoints.

The whole 113-local evaluator and public maximum still need their scope/loan
conditions discharged along every source path and finite budgets composed across
recursive calls. Dynamic regions/destructor instances and the other planning
targets remain open. This does not close W06-C3/SRC-01 or the full goal.

## Call-free backend independence and recursive choice

`SourceCallingNoCalls.lean` proves `Calling.{exec_noCalls,invoke_noCalls,
guardedInvoke_noCalls}`. Actual call-free code has identical execution under any
two callee implementations, including its complete world, packet and cost or
failure. Reference preparation, guards, routing, entry and cleanup stay in the
existing executor. Calls are excluded by the existing `noCalls` predicate;
unsupported routing and failing physical guards are not made successful.

`SourceRecursiveChoiceTotality.lean` uses that equality to transfer constructed
choice to arbitrary backends (`Choice.invoke_total_with`) and the actual
recursive dispatcher (`Recursive.{run_choice_total,original_choice_total}`).
One unit of recursive call fuel suffices for choice, even with zero remaining
callee fuel or readback budget. The generic program endpoint requires the actual
pinned choice declaration at its lookup; the original-program endpoint derives
that fact from the existing kernel certificate.

Both retain the exact native result/tie rule, full `Choice.cost`, readable
output, protected caller bytes and complete output/actual-caller/external owner
resources with live-Box coverage. Initial independent readability, complete
ownership, protected-read membership and input-owner/suspended-loan separation
remain explicit. There is no universal evaluator/maximum totality conclusion.

## Reconstructing the actual suspended caller

`SourceCallRetainedContext.lean` proves complete `Inventory.unique` from the
existing canonical executable inspection. `Frame.restore_empty` restores an
empty destination binding to its derived context, covering that stack root in
addition to retained reads. `Activation.preserve_call_context` then transports
the full suspended activation through precisely the guards used by the existing
call executor: remaining reads, old caller reads and the destination root.

`Derived.RootLoansAllowed.transport` transports the represented remaining and
caller inventories and uses their complete uniqueness to recover the same loan
permission after the callee. It requires no caller-supplied post-callee frame,
rescan oracle, pairwise-disjoint shared graphs or unique symbolic frame names.
The empty-destination and initial loan conditions remain necessary inputs to
the later guarded write.

## Stable whole helper calls

`SourceHelperCallTotality.lean` proves `Derived.call_run` for composition of
already constructed actual child operations. `call_ready_from_values` derives
the selected typed input domain from an independent local source argument step
and independently typed argument values, using determinism of the existing
addressed/source operand correspondence.

`Derived.helper_call_stable` constructs the whole call for any of the eight
helpers/intrinsics. It derives current and actual suspended scans, executes the
arguments once, derives their readable packets, complete input footprint and
post-argument owner partition, and obtains sufficient joint stable helper bounds.
The callee protects the actual remaining reads and destination root; the new
context lemmas reconstruct the returned active frame and transport its loan
permission. Independent source typing gives the returned packet type, and the
closed output type discharges its destination loan check. `store_complete`
constructs the actual write. Existing complete call contracts then retain valid
caller/active/world state, full owner-frame/coverage and the exact source action.

The endpoint provides fixed fuel/readback thresholds and one fixed final world,
activation and full cost for every larger pair of bounds. Initial valid storage,
complete ownership, the local source argument step, independent argument types,
a closed output type, an empty bound destination, selected move permissions and
its represented root-loan permission remain explicit. Helpers do not acquire
choice's input-owner/loan separation premise: insertion/query/shared aliases
permitted by the existing helper contracts stay permitted. Generic boxing of
reference-containing values remains outside this closed-output sufficient rule;
the earlier general packet/store loan contracts remain available.

`SourceRecursiveHelperCallTotality.lean` proves `Derived.call_callee_congr` for
the actual selected function and `Recursive.run_helper` for positive call fuel.
`Recursive.original_helper_call_stable` transfers the same constructed whole
helper call and exact source action to the actual original recursive dispatcher
at fixed sufficient joint thresholds. Unrelated interpreted functions are not
restricted to helper behavior.

## Whole recursive choice call steps

`SourceChoiceCallTotality.lean` defines `Derived.ArgumentsLoansAllowed` on the
owners actually extracted by the argument operation and the actual post-argument
suspended loans. This is an independent semantic transfer permission. It does
not assert a successful parent/callee call, desired result, post-state or
disjointness of every active owner from every shared read.

`packets_two_values` reconstructs the two physical packets from their independent
source values. `Derived.choice_call_total` derives the actual scans, argument
packets, full owner partition and guarded-read membership, obtains the now-total
recursive choice callee, transports the retained frame/loan permission, and
constructs its destination write. The resulting local mask contains the exact
native selected embedding. The call retains its local instruction charge plus
the exact complete choice cost, the corresponding source action, active/caller/
world validity and complete output/caller/external ownership/coverage.

Any readback budget and positive choice fuel suffice. Independently materialized
native argument values, valid storage, complete ownership, selected argument
move permissions, the empty destination and its root-loan permission, and
`ArgumentsLoansAllowed` remain explicit. Deriving these facts at each actual
evaluator call site, especially fresh-copy/result transfer and reference last
use, remains required. These rules do not prohibit allowed query/table/insertion
aliases elsewhere in the evaluator.

No maintained Rust, generated Charon/Aeneas output, parser, interpreter,
independent mathematical specification, original source hypothesis, cost
currency or pin changed. Symbolic storage/Box retirement and source-operation
counts do not establish physical allocator time, peak residency or optimized
production complexity.

## Maintained consumers and validation

`Tests/SourceAddressedExpressions.lean` constructs a whole recursive Box call
from a selected owned payload move. The original Box shell remains owned;
an inline sibling and the suspended caller's scalar retain their shared aliases.
The new rule supplies stable whole-call success, the exact source action and
complete final owner resources without a successful helper call or store input.

`Tests/SourceAddressedControl.lean` constructs a parent call to actual recursive
choice for arbitrary native score pairs and arbitrary readback budgets, with
one or more callee fuel. Independent input footprints/ownership, a real fresh
destination, closed post-argument masks and derived loan permissions supply the
inputs. The returned local has the native result and exact full call cost with
complete final ownership. The earlier whole guarded-entry consumer remains.

The 4,022-job root build and all five affected suites pass without new
module/test warnings: both modified consumers, `SourceHelperCalls`,
`SourceOwnerLifecycle`, and `SourceRecursiveExecution`. The latter reruns all
eight maintained runtime cases: cold empty/nonempty evaluator and public maximum,
warm cache hit, both checked-add overflows and both recursive failure paths.
They compare complete source/native value/table/cost, preserve caller storage,
and check complete Box ownership/coverage and callee cleanup. These finite
runtime cases do not establish universal recursive evaluator totality.

The 1,401-distinct-endpoint audit includes all 18 new theorems and retains only
`propext`, `Classical.choice` and `Quot.sound`. Eight selected `leanq` statement
seeds cover 1,125 unique declarations with zero unknown references; this is
selected statement inspection, not a whole-library export. All seven build
caches are bind-mounted over guest-local ext4.

CI still lists 47 Lean suites. No new full-suite/native-WP/Python/Rust run is
claimed. Full 47-suite/native-WP/nine-Python evidence remains at `d49f638` and
thirteen ordered Rust tests at `823df34`; the eight recursive runtime cases are
freshly rerun here.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-constructed-calls-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_noCalls \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_choice_total \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Frame.restore_empty \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Activation.preserve_call_context \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.RootLoansAllowed.transport \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.helper_call_stable \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_helper_call_stable \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.choice_call_total
```

Machine-local logs: `/var/tmp/subtree-constructed-calls-{build,axioms,
statements}.log`, `/var/tmp/subtree-constructed-calls-statements.json`, and
`/var/tmp/subtree-call-{expression-tests,control-tests,helper-tests,lifecycle-tests,
recursive-runtime}.log`.

## Next priority

Construct actual evaluator paths, starting with the common lookup prelude and
cache-hit/empty-query exits, then pair/pair recursion and both overflow/failure
branches. Derive source scope, empty destinations, initialized operands, selected
move/root-loan and transferred-owner permissions from actual native inputs,
copy/result freshness and reference last use. Compose the stable helper bounds
and finite recursive induction into whole interpreted physical success, then
the public maximum and cold-table teardown. Dynamic parsed regions/destructor
instances, wrappers/input policy, global resources/G3 and every other planning
target remain. The full goal stays active.
