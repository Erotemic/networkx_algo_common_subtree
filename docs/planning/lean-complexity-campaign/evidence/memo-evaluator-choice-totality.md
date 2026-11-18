# Whole pinned choice totality

Date: 2026-11-18. Baseline: `ae32513` on `Droschinsky-algos`. Six proof
modules add 27 public checked theorems. Actual parsed choice entry, its complete
body, both winner branches, losing-value destruction, return and checked stack
closure are now constructed for arbitrary native embeddings. No successful
addressed parent execution or expected final heap is a premise.

`Choice.invoke_total` constructs `Calling.guardedInvoke` on
`CallingCertificate.originalChoice` with the exact native selected result and
existing full `Choice.cost`. It retains readable output, world validity,
protected caller bytes, an output footprint, complete unique/live Box ownership
for output/actual callers/external owners, and coverage of every live Box.
The existing native tie rule selects the first input. Helper call fuel and ghost
readback budgets are arbitrary, including zero: this actual body calls no helper.

This is a sufficient legal-transfer contract. Independently readable native
input packets, valid actual callers, complete initial owner-frame/coverage and
an input footprint remain explicit. **Input owners must be disjoint from the
actual suspended caller loans.** Protected addresses belong to the actual
caller read inventory. This excludes destroying an input still borrowed by a
suspended caller; it is stronger than a branch-specific condition on only the
loser. It does not require pairwise-disjoint shared read graphs, distinct
symbolic frame IDs, an empty caller stack, a supplied whole source/native run,
or a supplied physical-success/readback-depth bound.

The recursive evaluator must still derive this permission for its fresh copied
or recursively returned choice arguments. Query/table/insertion aliases remain
allowed by the earlier general contracts. Do not replace their legal aliasing
domain with this closed-input sufficient condition.

## Closed actual machines

`SourceClosedMachine.lean` defines `ClosedState` from independent partial typing
and closed types. Its set/clear laws retain the invariant, and `forget`/
`forgetRefs` prove that the existing reference-view preparation is exactly the
identity on these states. The original calling executor still prepares every
action; no interpreter or guard has changed.

`Derived.action_owner_subset` uses the exact existing complete owner partition,
preserved actual caller owners and final uniqueness. Every owner remaining in
the active frame came from its previous active owners. Retirement cannot
silently import caller or external owners.

`ClosedMachine` carries valid storage, complete ownership/coverage, closed
partial masks, separate roots, fresh roots above the original memory boundary,
preserved original caller reads and owner/old-loan disjointness. `advance`
transports those resources through actual constructed actions. Its local move,
RHS, root-loan and drop-loan lemmas derive permissions from the actual inventories.
Its storage-live/dead, assignment, drop and boolean-inspection endpoints construct
the existing raw operations and retain the invariant. Local-only move syntax
is explicit; these rules do not pretend to handle arbitrary nested move routes
without the earlier selected-route contracts.

`Calling.exec_noncall_step` and `ClosedSteps.exec` compose these actual primitive
runs through the unchanged calling control and costs. `ClosedSteps` is a proof
trace of actual operations, not a replacement program evaluator or parser.

## Constructing the pinned body

`SourceChoiceForward.lean` proves `prelude_complete`. The actual seven actions
allocate local roots 0, 3, 4 and 5, copy both bounded native scores, then move
locals 4 and 5 into the comparison stored in local 3. Arguments retain their
original masks and roots; both score masks are empty. Complete owner/loan
resources and all scope facts are constructed at each point.

`SourceChoiceBranchForward.lean` proves `branch_complete` for either input.
Both empty score roots retire, then the selected native embedding moves into
local zero. Its existing Box identities transfer without copying or allocation.

`SourceChoiceTailForward.lean` proves `tail_complete`. The consumed comparison
root retires, both input locals drop (one is already empty), both input roots
retire, and the actual checked return extracts local zero. Every callee mask is
empty afterward. Remaining roots retain freshness and caller separation.

`SourceChoiceBodyForward.lean` combines these components with the actual shared
switch routing. `selected_complete` joins an arm with its continuation;
`body_complete` constructs the complete actual calling execution for arbitrary
native inputs and an arbitrary callee implementation. No call occurs in this
body. Strict score comparison takes the second arm only when it wins; equality
follows the established first-input tie rule.

`SourceChoiceTotality.lean` derives closed initial masks from native result
typing, constructs real argument entry with the actual six-local declaration,
invokes `body_complete`, derives readable/global owner resources from the
existing calling contracts, and constructs `close_total`. Fresh-root bounds
and preserved caller inventories discharge every closure loan check. Only then
does it reuse `invoking_refines` to obtain the exact established full cost and
native tie/result relation. `invoke_total` includes the real guarded-entry check.
The theorem currently instantiates the existing helper callee; the arbitrary
callee body theorem is available for subsequent recursive-dispatch composition.

No Rust, generated Charon/Aeneas artifacts, parsers, interpreters, independent
specifications, source hypotheses, cost currencies or pins changed. Symbolic
storage/Box retirement is not a proof of physical allocator deallocation,
allocator time, peak residency or optimized production complexity. Dynamic
parsed region/destructor-instance interpretation and W06-C3/SRC-01 remain open.

## Maintained consumers and validation

`Tests/SourceAddressedControl.lean` now consumes `invoke_total` for arbitrary
score pairs and arbitrary helper budgets, with a nonempty first word owning two
Boxes. It supplies independent input read graphs, footprints and complete
ownership, then obtains actual parsed entry/body/closure, the native selected
result/full cost and complete output ownership. It supplies no successful run.
Existing concrete winning-second, winning-first and tie checks, partial-tag
inspection, early returns, unsupported routing and borrowed-return rejection
remain. `SourceOwnerLifecycle` retains the live-alias drop rejection and
fresh-root/frame-collision consumers. `SourceCallingProgram` retains actual
calling/parsed-entry regression coverage.

The 4,016-job root build and all three affected suites pass without new
module/test warnings. The 1,383-distinct-endpoint audit includes all 27 new
theorems and retains only `propext`, `Classical.choice` and `Quot.sound`. Eight
selected `leanq` statement seeds cover 1,124 unique declarations with zero unknown
references. This is selected closure inspection, not a whole-library export.
All seven build caches remain bind-mounted over guest-local ext4.

CI still lists 47 maintained Lean suites. No new full-suite/native-WP/Python/
Rust or runtime-execution run is claimed. Full 47-suite/native-WP/nine-Python
evidence remains at `d49f638`; runtime cold/warm/overflow/failure evidence at
`a56e701`, and thirteen ordered Rust tests at `823df34`.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceCallingProgram.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-choice-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.ClosedState.forgetRefs \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.action_owner_subset \
  SubtreeProofs.Rust.SourceEval.Addressed.ClosedMachine.advance \
  SubtreeProofs.Rust.SourceEval.Addressed.ClosedMachine.dropLoans \
  SubtreeProofs.Rust.SourceEval.Choice.prelude_complete \
  SubtreeProofs.Rust.SourceEval.Choice.branch_complete \
  SubtreeProofs.Rust.SourceEval.Choice.body_complete \
  SubtreeProofs.Rust.SourceEval.Choice.invoke_total
```

Machine-local logs: `/var/tmp/subtree-choice-{build,control-tests,lifecycle-tests,
calling-tests,axioms,statements}.log` and
`/var/tmp/subtree-choice-statements.json`.

## Next priority

Compose choice totality with the actual recursive dispatcher. Construct actual
argument/callee/result-store calls from independent input, scope and loan facts,
then discharge all paths of the 113-local recursive evaluator and public maximum
with sufficient stable call/readback budgets. Derive fresh-choice input transfer
permissions from the actual copy/recursive-result owner ledgers; retain allowed
query/table/insertion/shared aliases. Dynamic parsed regions/destructor instances,
native public maximum/cold-table teardown, wrappers/input policy, global
resources/G3 and every other planning target remain. The full goal stays active.
