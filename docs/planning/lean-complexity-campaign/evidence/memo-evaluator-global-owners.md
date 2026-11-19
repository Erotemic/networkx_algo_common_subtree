# Global ownership for recursive source execution

Baseline: `8d2f3d9` on `Droschinsky-algos`. Eleven proof modules compose
complete owner resources through all actual helpers, caller argument/result
transfer, selected control, parsed entry, return cleanup and recursive dispatch.
The native evaluator endpoint now combines its existing independent result/table
and full-cost refinement with complete returned/caller/external ownership.
Concrete success remains explicit. No production Rust, generated artifact,
interpreter, source/native specification, hypothesis, cost or pin is changed.
W06-C3/SRC-01 and the full planning goal remain open.

## Exact helper ownership without height assumptions

`LookupOwnerTransfers.lean` strengthens the existing separation transfers with
`Heap.Owners.Conserves`. Every complete old occurrence list is transported to a
complete resulting list up to permutation. These lemmas retain multiplicity;
they require no initial uniqueness assumption and do not deduplicate owners.
Local moves, scalar/shared copies, borrows, aggregates, boolean scrutinees,
disposable clobbers and return cleanup all conserve the exact owner ledger.
Plain values add no owners; discarded disposable locals lose no owners.

`LookupOwnerGrowth.lean` defines `fresh` as the actual appended memory interval
and `Grows` as an existing-memory extension plus an exact complete ownership
ledger. Sequential growth composes the adjacent fresh intervals. A retained
cell frame carries the same old owner occurrences, including duplicate
occurrences if the initial list has them. `action_grows` and `guarded_grows`
combine the unchanged helper interpreter with its already checked disposable-
local guards and independent local/type constraints. Every old occurrence is
transferred and every fresh Box identity occurs exactly once.

`SourceHeapOwnerDrivers.lean` uses a shared `ConservingDriver` proof record.
Its fields describe existing zero/Box behavior and actual successful ordinary
execution's checked guarded trace, local bound and type constraints. It adds no
interpreter or desired owner/output conclusion. The real lookup and memo
instances reuse their existing pinned frame/type certificates. Fuel induction
proves `lookup_grows` and `MemoSource.Heap.run_grows` for every successful fuel,
without a native height, expected answer or supplied intermediate owner ledger.
The generic Box case transfers its entire actual payload footprint.

## Mixed worlds, profiles and all eight helper outputs

`SourceOwnerFresh.lean` separates old owners from the actual fresh Box suffix,
preserving complete owner-frame and live-Box coverage resources. All new suffix
addresses are live and Box-class; old stack/Box classes and live flags remain.
`boxSuffix_owner_transfer` replaces the transferred input list with the exact
returned list and fresh suffix while retaining the external owner ledger.
Well-formed-world lemmas identify ordinary Box allocation and unchanged worlds
with their corresponding suffix constructions.

`SourceOwnerHelperResults.lean` connects both exact old driver ledgers to the
actual `finish`/`readPacket` result, retaining concrete cell identity and complete
footprints. `SourceOwnerHelperProfiles.lean` derives the existing conservative
helper ownership profiles from independently typed actual readable packets.
Shared/scalar inputs are plain; insertion's table remains potentially owning.
The old sufficient native helper height/readiness conditions are absent.

`SourceOwnerCallees.lean` defines `Derived.CallsOwn`: typed readable actual
arguments, valid actual suspended callers, initial complete owner-frame/coverage
and successful callee execution yield a complete output footprint and final
owner-frame/coverage over output, actual callers and external owners. It contains
no supplied post-state, desired output or parent execution result.

`Helpers.callee_owner_ledger` proves exact old-input-plus-fresh output footprints
for all six actual ordinary helpers and both intrinsics. `callee_owns` discharges
the complete ownership contract for the actual dispatcher. Insertion transfers
its old table once; `boxNew` transfers its whole payload and adds one fresh Box;
checked addition transfers no owners. Actual typed inputs derive the local
profiles. Shared query/result references may alias owned table/input graphs.

## Actual calls, control, entry and closure

`SourceOwnerCallTransfer.lean` proves `Derived.store_owner_resources` and
`call_owner_resources`. The real one-pass argument extraction obtains the input
footprint and complete remaining owner partition. The callee receives the real
post-argument activation followed by the original callers. Its actual output
contract and protected-byte contract derive the returned context and output
packet; the existing guarded destination store completes transfer. No guard
list, intermediate owner list or post-callee frame is supplied to the complete
call theorem. Actual final caller owner identities come from retained resources.

`SourceOwnerControl.lean` defines `Derived.Flow.OwnerResources` for next/returned
flows. A returned packet is counted separately from still-initialized locals.
Scrutinees conserve the exact owner list; boolean extraction owns nothing.
`Calling.instruction_owner_resources` composes supported non-call actions and
the actual call step. `exec_owner_resources` follows existing selected control,
joins and early returns, preserving complete global ownership/coverage and the
actual caller stack. Certified unused shared-reference views retain exact owner
identities via the preceding `Activation.forgetRefs_owners` theorem. Skipped
branches/joins do not acquire readiness obligations.

`SourceOwnerInvoke.lean` combines real parsed parameter entry, calling control,
return extraction and successful checked stack closure. Complete packet owners
become actual parameter-local owners. Closure checks no active owners remain
and that returned/caller reads do not escape through retiring roots; its existing
Box-liveness preservation retains output and actual caller ownership. Both
`invoke_owner_resources` and `guardedInvoke_owner_resources` use the actual
parsed declaration/count. Entry/cleanup and source costs remain unchanged.

## Complete recursive and native endpoints

`SourceOwnerRecursive.lean` exports:

- `Recursive.run_owns`: fuel induction discharges all actual helper and parsed
  choice/evaluator/maximum calls, using the real post-argument suspended stack.
  The independent actual types and existing typed source/cost correspondence
  derive selected call domains and parsed entry readiness.
- `original_owns`: specialize that complete contract to the pinned actual
  program. Given initial unique live Box owners and coverage of every live Box,
  successful actual execution returns a complete output footprint and final
  unique/live Box owners covering output, actual callers and external owners.
- `original_evaluate_owned_refines`: arbitrary native queries and warm tables
  retain the completed native result/table, exact `Evaluation` full-cost
  relation, readable output, well-formed world and protected caller bytes,
  together with complete output ownership and the global owner-frame/coverage.

The initial ownership resources are explicit and necessary; readability alone
allows duplicated owning pointers. Shared read aliases remain allowed. These
statements take no native height, supplied `Recursive.Ready`, desired source
answer or expected output ownership as a premise. They still require actual
concrete success and the original readable/type/world/native input conditions.
Original sound-cache hypotheses remain necessary for separate optimality claims.

## Consumers and adversaries

- `Tests/SourceTypedCalls.lean` consumes the new output contract on comparison
  at fuel one although the old whole-word height bound fails. The complete
  external ledger covers the four old Boxes. Existing zero-fuel/readback-budget
  failures and the necessary u32-width adversary remain.
- `Tests/SourceHelperCalls.lean` consumes complete call ownership on actual
  warm-table insertion with shared keys/result pointing into the owned table.
  Actual argument execution derives typed readiness, and the result store
  retains all transferred owners and complete fresh-Box coverage.
- `Tests/SourceOwnerFrames.lean` consumes whole `boxNew` call transfer on the
  nested payload, including enclosing/sibling owners, an actual caller-owned
  Box and allowed shared aliases. The final active owners are `[0,9,1,3]` and
  caller owners `[7]`; the actual new Box at address 9 is live.
- `Tests/SourceRecursiveCalls.lean` consumes `original_owns` on the actual choice
  run which destroys both losing Boxes, closes all callee roots and retains
  the scalar/aliased-reference caller. It also consumes the stronger native
  evaluator endpoint on arbitrary query/warm-table inputs with explicit initial
  owner resources, preserving the full native result/cost and protected bytes.
- `Tests/SourceRecursiveExecution.lean` adds runtime checks for complete output/
  caller owner uniqueness, live Box classification and coverage on both actual
  nonempty evaluator and public maximum runs. Existing complete source values,
  costs, caller bytes/liveness and cleanup checks remain. These executable
  checks complement the general kernel proof; they do not establish totality.

## Remaining scope

Conditional complete global ownership through the actual recursive execution is
now checked. Next prove sufficient source-call and ghost readback budgets and
physical success of every move/write/drop/storage/return/cleanup check on legal
native inputs/warm tables. Compose the complete actual owner invariant with loan
coverage and permitted aliases to derive those permissions, rather than assume
the successful parent run. Dynamic interpretation of actual parsed region
binders and destructor instances, including explicit compiler/runtime/allocator
boundaries, also remains. Logical retirement is not a physical free-cost theorem.

Finish the native public maximum/cold-table teardown theorem, separate wrappers/
input policy, global time/space, G3 and the other LV/Droschinsky/software/release/
application targets. The D12 source-operation boundary is unchanged. No complete
W06-C3, SRC-01, production runtime/physical space or full-goal closure is claimed.

## Validation and reproduction

The root build passes 3,988 jobs. All eleven new modules and affected kernel
consumers compile warning-free; the root build replays pre-existing unrelated
warnings. All 47 maintained Lean suites, native WP and nine Python reifier tests
pass. The evaluator/maximum runtime suite is tracked separately from the other
46 maintained suites to avoid repeating its long-running execution. Its new
complete owner checks pass alongside the unchanged cold empty/nonempty source
values, costs, caller bytes and cleanup checks.

The 1,243-endpoint axiom audit includes all 57 new public theorems and retains
only `propext`, `Classical.choice` and `Quot.sound`. Shared `leanq` inspection
covers 1,388 unique declarations from ten selected seeds with zero unknown
references. This is the selected statement closure, not the entire library.
The inspected native endpoint retains concrete success and initial complete
ownership/coverage premises and has no `Recursive.Ready` premise. All seven
Lean/Rust cache mounts remain VM-local ext4. Rust/generated files did not change;
the thirteen ordered Rust tests remain evidence from `823df34`, not a fresh run.

From the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceTypedCalls.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerFrames.lean)
(cd proofs && lake env lean Tests/SourceRecursiveCalls.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
# Run every remaining maintained suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
python3 proofs/checks/test_lookup_source_reifier.py
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-global-owner-statements.json \
  SubtreeProofs.Rust.LookupSource.Heap.Owners.guarded_grows \
  SubtreeProofs.Rust.LookupSource.Heap.Owners.lookup_grows \
  SubtreeProofs.Rust.MemoSource.Heap.run_grows \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.callee_owner_ledger \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.callee_owns \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.call_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.invoke_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.run_owns \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_evaluate_owned_refines
```

Machine-local evidence: `/var/tmp/subtree-helper-owner-{build,execution-tests,
recursive-tests,typed-tests,helper-tests,frame-tests}.log`,
`/var/tmp/subtree-global-owner-{regression,axioms,statements}.log` and
`/var/tmp/subtree-global-owner-statements.json`.
