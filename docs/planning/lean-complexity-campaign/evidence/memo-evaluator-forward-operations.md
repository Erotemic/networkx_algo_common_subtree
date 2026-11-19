# Forward assignments, move routes and return extraction

Date: 2026-11-18. Baseline: `a446876` on `Droschinsky-algos`. Five proof
modules add 23 checked public theorems. Actual stores, assignments, selected move
routes, return extraction and switch inspection now have forward contracts.
They construct addressed runs from valid input frames, complete ownership and
semantic loan permissions. Assignment and inspection retain an explicit
independent local source RHS/scrutinee step; no successful addressed parent,
whole source/native parent run, desired final heap or supplied post-RHS frame is
an input. Complete pinned choice/evaluator/maximum success and the full planning
goal remain open; this does not close W06-C3/SRC-01.

## General stores, including reference packets

`SourceStoreTotality.lean` proves `OwnerFrame.of_append_right` for temporary
permission reasoning, without claiming that removing owners preserves global
Box coverage. `Graph.stack_root_not_read` uses the complete read partition,
packet footprint and Box classes to reduce packet/destination conflicts to its
actual shared loans. `PacketLoansAvoid` describes those packet loans;
`StoreLoansAllowed` combines them with represented remaining and actual caller
loans. Neither predicate assumes successful storage or its desired post-state.

`PacketLoansAvoid.of_closed`, `StoreLoansAllowed.of_parts` and
`StoreLoansAllowed.of_closed` discharge closed packet cases or combine independent
permissions. The general `Derived.{store_complete,store_total}` also covers
reference packets. An empty bound destination, valid storage, complete packet/
active/caller/external ownership, separate roots, readable packet and represented
loan facts construct the actual guarded write. Packet footprints and owner
classes discharge owned read conflicts; remaining stack classes and separate
caller roots discharge root conflicts. The stronger endpoint retains final
activation/caller/world validity, protected caller bytes and complete final
owner-frame/live-Box coverage. It does not require disjoint shared read graphs.

## Owned routes and loan-only move permissions

`SourceMovePermissions.lean` proves `Rep.take_locate_root` for every successful
source take and corresponding actual pointer route. Partial owned field/deref
routes reach either the starting local root or a currently owned Box. Shared
referents cannot be moved through; emptied fields and retained Box shells keep
their existing semantics.

`Activation.move_route` lifts the result to the complete finite activation.
`move_not_in_caller_reads` uses global owner uniqueness, Box/stack classes and
separate actual roots to reduce the caller read guard to actual shared loans.
`Addressed.{allowed_local,allowed_local_from_loans,move_allowed_from_loans}`
construct the existing physical operand permissions. The local rule permits a
whole owned value to move when its own stack root is unborrowed; it does not ban
loans into every internal address. The general rule constrains the selected
route's actual root, preserving unrelated query/sibling/shared aliases.

## One-pass assignments and actual returns

`SourceAssignmentTotality.lean` defines `ExpressionLoansAvoid` over actual
possible RHS packets. This is a semantic permission on their shared loans,
not an assertion of assignment success, final heap validity or an expected
parent result. `of_closed` derives it from the independent local source RHS
step and a closed output type.

`Derived.{assign_complete,assign_total}` combine existing forward RHS simulation,
selected move permissions, an empty post-RHS destination, represented remaining/
caller root-loan permissions and packet loan permissions. Actual RHS evaluation
occurs once. The post-RHS frame, complete temporary owners, readable packet and
actual remaining inventories are derived. The constructed assignment retains
its original source `Step` and full cost, caller/world validity and complete
owner resources. `assign_complete_closed` supplies the common closed-output
case; the general endpoint continues to support shared-reference RHS values.

`SourceReturnTotality.lean` defines `ReturnLoansAllowed` over represented active/
caller loans and proves `of_closed_preserved` from independent closed locals,
preserved caller reads and a fresh output root. `Derived.{returnValue_complete,
returnValue_total}` construct actual local-zero extraction from a bound root and
independent local materialization. They retain the exact source return and cost,
clear its initialization mask, preserve a readable complete output footprint and
split the global owner-frame/coverage between output, remaining activation and
actual callers/external owners. Stack cleanup is still a separate operation,
now composable with the preceding forward `Storage.close_total` theorem.

## Retained-tag and boolean inspection

`SourceScrutineeTotality.lean` defines `ScrutineeAllowed`: retained discriminants
need no move permission; boolean operands use the existing operand permission.
`Addressed.scrutinee_complete` constructs actual inspection from the independent
local source step. A discriminant needs a retained node tag, not materialization
of moved fields. Boolean reads/moves use actual operands and their concrete
boolean cells. `Derived.{scrutinee_complete,scrutinee_total}` derive actual scans
and preserve the resulting valid activation and complete owner resources.
Routing, selected branches, early return and their costs remain in the existing
shared control executor; unsupported routes are not declared successful.

No Rust, generated Charon/Aeneas artifacts, interpreters, specifications, source
hypotheses, resource currencies or pins changed. Tracing, scans and metadata
reasoning remain ghost work. Source operation/destructor counts do not become
physical deallocation, allocator-time, peak-space or production runtime bounds.

## Maintained consumers and validation

`Tests/SourceAddressedExpressions.lean` constructs a derived shared-reference
assignment with an existing sibling alias and a caller's aliased scalar. It
checks the original source step and complete final owner/coverage resources.
A selected owned payload move is allowed alongside those unrelated aliases;
a packet pointing back into its own destination fails `PacketLoansAvoid` even
though it owns no Boxes. These permission facts are derived independently of
successful assignment or store execution.

`Tests/SourceAddressedControl.lean` constructs inspection of a partially moved
node tag. It also constructs fresh scalar return extraction and composes it with
actual checked cleanup, verifying root retirement and retained output/complete
owner resources. Existing early-return, unsupported routing and borrowed scalar
return rejection cases remain.

The 4,010-job root build and both affected suites pass without new module/test
warnings. The 1,356-endpoint audit includes all 23 new theorems and retains only
`propext`, `Classical.choice` and `Quot.sound`. Eight selected `leanq` statement
seeds cover 414 unique declarations with zero unknown references. This is
selected statement coverage, not a whole-library export. All seven build caches
remain bind-mounted over guest-local ext4.

CI still lists 47 maintained Lean suites. No new full-suite/native-WP/Python/
Rust or runtime-execution run is claimed. Full 47-suite/native-WP/nine-Python
evidence remains at `d49f638`; runtime cold/warm/overflow/failure evidence at
`a56e701`, and thirteen ordered Rust tests at `823df34`.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-forward-operations-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.store_total \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Rep.take_locate_root \
  SubtreeProofs.Rust.SourceEval.Addressed.allowed_local_from_loans \
  SubtreeProofs.Rust.SourceEval.Addressed.move_allowed_from_loans \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.ExpressionLoansAvoid.of_closed \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.assign_total \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.returnValue_total \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.scrutinee_total
```

Machine-local logs: `/var/tmp/subtree-forward-operations-{build,axioms,
statements}.log`, `/var/tmp/subtree-forward-{expression,control}-tests.log` and
`/var/tmp/subtree-forward-operations-statements.json`.

## Next priority

Construct the entire actual pinned six-local choice execution and guarded
entry/cleanup on legal native inputs. Maintain fresh roots and scope, preserved
old caller inventories, complete owners, and their relation to the initial
owned inputs. Derive its closed-local and discarded-owner loan permissions at
each selected source point; do not assume parent execution. Compose the existing
exact native tie/result/full-cost refinement afterward. Then discharge actual
argument/callee/result-store calls and all source-path permissions through the
113-local recursive evaluator and public maximum, combining the already proved
stable finite budgets. Preserve allowed query/table/insertion/shared aliases.
Dynamic parsed regions/destructor instances, public cold-table teardown,
wrappers/input policy, global resources/G3 and all other planning targets remain.
