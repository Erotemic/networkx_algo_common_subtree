# Caller preservation and recursive addressed dispatch

Baseline: `2b4f628` on `Droschinsky-algos`. W06-C3/SRC-01 and the full planning
objective remain open. Production Rust, generated artifacts, source semantics,
independent native specifications and toolchain pins are unchanged.

Subsequent follow-up: [certified unused shared-reference views](memo-evaluator-loan-endings.md)
repairs the operational failure recorded below at this baseline. The maintained
nonempty evaluator and maximum regressions now succeed with complete source
value/cost equality. The historical failure and reproduction here refer to
`57deada`; universal physical success and the broader C3 obligations stay open.

## Stored caller data, not only representation

The existing non-call action and call proofs already construct guarded write/
retire transitions. Their exported suspended-resource conclusions now retain
`Preserves world final resources.reads` alongside the old scan equation and
exact final caller inventories. This strengthens `Derived.Step`, `assign_spec`,
`call_spec` and `Calling.Step`; no source statement or hypothesis is weakened.
The two existing inventory/storage consumers also require the stronger result.

`SourceCallerResources.lean` reuses actual resource tracing to prove:

- `PartialGraph.guards_unique`, `LocalResources.reads_unique`,
  `Inventory.reads_unique`, `Callers.reads_unique`: the complete represented read
  lists are deterministic at a fixed world, including transitive shared reads.
- `Inventory.reads_subset`, `Activation.context_reads_subset`: the computed
  destination-excluding inventory is covered by the complete active inventory.
- `Scanned.binding_reads`, `Activation.call_guards_covered`: the protected
  destination root and all remaining/caller reads are covered by the actual
  post-argument activation followed by the original suspended callers.

The last endpoint is an input-side coverage theorem for the already constructed
post-argument frame. It does not assume a desired callee result or provide a
replacement caller stack.

`SourceEvalCallerPreservation.lean` exports `Callers.scan_reads`, both
`Derived.Step.preserves` and `Calling.Step.preserves`, then composes transitions:

- `Calling.exec_preserves` retains complete stored caller bytes, classes and
  liveness through instructions, selected branches, continuations and early
  returns. Rescans are matched to transported inventories by read-list uniqueness.
- `Calling.invoke_preserves` includes fresh parsed argument entry and checked
  zero-owner/output-escape stack cleanup in that same preservation statement.

These use the existing executor and its verified local callee contract. Input
readiness and successful concrete execution remain explicit. Representation
alone is not substituted for stored-byte retention.

## Recursive callee contract

`SourceEvalGuardedEntry.lean` checks supplied guard membership in the computed
actual suspended caller read list before invoking a declaration. Its
`guardedInvoke_complete` discharges that check from independent coverage;
`guardedInvoke_spec` combines complete source run/cost, readable output,
well-formedness and `Preserves` on the supplied protected addresses. Duplicate
read aliases remain allowed. The parent call's computed guards have the
coverage established above.

`SourceEvalRecursiveCalls.lean`, namespace `SourceEval.Addressed.Recursive`,
executes the existing six ordinary helper backends and both intrinsics. Choice,
evaluator and maximum go through actual parsed declaration lookup, guarded
entry, shared calling control and checked return cleanup. Every recursive
callee gets the actual post-argument suspended stack. Call fuel decreases only
at recursive entry, matching the existing source run; the separate ghost output
readback budget is unchanged.

Public endpoints are `interpreted_nonintrinsic`, `run_zero`, `run_respects`,
`original_respects`, `ready_noCalls` and `ready_original_choice`.
`CallingCertificate.original_codes` binds every actual typed declaration to the
pinned source body. `choice_lookup` reuses the actual choice accessor. No parser,
helper implementation or source interpreter is copied.

`Recursive.Ready` starts from the completed native helper shapes/depth bounds.
For interpreted bodies it composes those input conditions through the actual
selected concrete paths for each suspended caller stack. It contains no desired
source result, complete parent source-success premise or desired post-argument
context. `run_respects` proves the recursive `CallsRespect` contract by induction
on fuel from this domain, actual input readability/caller validity and concrete
success. It is not universal readiness or a guarantee that every physical check
passes. Source-operation costs remain unchanged; ghost scans and guard checks
are not additional production Rust work or a wall-time bound.

`SourceEvalRecursiveRefinement.lean` exports:

- `original_choice_refines`: the actual recursive dispatcher returns the existing
  native selected result/tie rule at exact `Choice.cost`, with readable output,
  world validity and protected caller-byte retention. Choice readiness is fully
  discharged from its actual call-free body.
- `original_evaluate_refines`: input readiness plus a successful actual recursive
  evaluator run retain exact native result/table, the established `Evaluation`
  source/native/full-cost relation, readable output and protected caller bytes.
  Arbitrary warm tables and overflow/failure outputs keep the old hypotheses;
  no cache-optimality claim is added without the original sound-cache premises.

## Consumers and an exposed lifetime gap

`Tests/SourceRecursiveCalls.lean` uses the pinned actual choice declaration with
one-step call fuel and zero helper-readback budget. A suspended caller owns a
scalar and a reference to that same scalar, so its read list includes aliases.
The invocation retires both losing Boxes and every callee stack root, retains
actual caller data/liveness and derives the independent native result/full cost
and caller validity from the recursive contract. Invalid guard coverage and a
retired transitive caller target fail. A general evaluator consumer retains the
explicit readiness obligation instead of supplying an expected parent answer.

`Tests/SourceRecursiveExecution.lean` is an executable regression, distinct from
the kernel-checked universal statements. It runs the actual 113-local evaluator
on a cold empty/empty query, including lookup, insertion, suspended callers and
cleanup. The exact native empty result and one-entry table agree with the pinned
snapshot source. Both report 271 source steps, two Box allocations and one
solver call. Only caller roots 0/1 and output Box owners 22/23 remain live.

A further actual run exposes the next operational obligation. For two input
words `Pair Empty Empty`, a cold table, call fuel 16 and readback budget 128, the
pinned snapshot evaluator succeeds with score 1, 2,615 source steps and five
solver calls. The current addressed recursive dispatcher returns no result.
The public maximum at fuel 17 similarly has snapshot result score 1 / 2,704
steps / five solver calls, while addressed execution returns no result.

Tracing with the existing `Control.execWith` and instruction primitives locates
the first failure in the second child evaluator's cache-hit branch:

```text
Evaluator.cacheHit: assign 12 (use (move (local 3)))
active owners = [46, 47]
active loans  = [1, 4, 46, 47, 61]
local 3's stack root = 61
local 6 still stores the earlier reference to that table
```

`Evaluator.start` creates local 6 before lookup. Its final dereference feeds the
lookup argument, but its `StorageDead` is later in `cacheHit`, after moving the
table. The current guard treats every initialized reference as an active loan.
Stored pointer bits and active borrow lifetime must be separated. This is not
fixed by more fuel/readback budget or by proving native input shapes.
The existing parsed region/binder certificates do not supply dynamic expiration;
body binder IDs must not be treated as statement offsets.

The proof suite includes a minimal Box-owner movement witness: a stored shared
reference produces the complete `[3, 0]` loan guard; guarded movement is rejected
while the unannotated snapshot action succeeds. The active-loan guard remains
intact. Its eventual use must be justified by actual loan activity/ending and
source correspondence, including continued storage, aliases, caller transfers
and destructor costs. No universal physical-success or C3 closure is claimed.

A compact reproduction of the actual nonempty failure, in a temporary Lean file
with an ordinary `import SubtreeProofs.Rust.SourceEvalRecursiveRefinement`:

```lean
open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

def word : BalancedWord := .Pair .Empty .Empty
def world : World := ⟨[.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1],
  .node .word 0 [], .node .word 0 [], .node .word 1 [.owned 3, .owned 4]], fun a =>
  if a = 2 then some (.stack 90 1 2) else if a = 5 then some (.stack 90 2 5)
  else if a < 6 then some .box else none, fun a => decide (a < 6)⟩
def caller : Activation := ⟨90, 3, fun s =>
  if s = 1 then some ⟨2, 2⟩ else if s = 2 then some ⟨5, 5⟩ else none,
  fun s => if s = 1 ∨ s = 2 then Slot.ofValue (encodeWord word) else .empty⟩
def packets : List ValueCell := [(.shared ⟨2, []⟩, .reference (encodeWord word)),
  (.shared ⟨5, []⟩, .reference (encodeWord word)), (.node .table 0 [], encodeTable .Empty)]
#eval (Recursive.original 128 16 world (List.range 6) [caller] .evaluate packets).isSome
#eval (SourceEval.run SourceEval.Certificate.original.body 16 .evaluate (packets.map Prod.snd)).isSome
-- Output at baseline 57deada: false, then true.
```

## Validation and remaining full scope

The full 3,956-job public build, all 43 maintained Lean suites, native WP and
nine Python tests pass. Both new suites and all maintained changed modules have
no diagnostics; existing unrelated root-build warnings remain. The axiom audit
covers 1,055 distinct endpoints, including all 25 new public theorems, using only
`propext`, `Classical.choice` and `Quot.sound`. Shared `leanq` exports 1,225 unique
elaborated declarations from six seeds with zero unknown references. Inspected
signatures retain independent input readiness and concrete success; choice
readiness is discharged, and guarded coverage derives retained caller bytes.
The known nonempty lifetime failure remains an explicit counterexample to
universal physical success, not a passing claim of C3 completion.

Reproduce from the repository root after preparing VM-local build caches:

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceRecursiveCalls.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Run every maintained Lean suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-recursive-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_preserves \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.guardedInvoke_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_respects \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_evaluate_refines \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_choice_refines \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Activation.call_guards_covered
```

Temporary machine-local evidence uses `/var/tmp/subtree-recursive-*.log`,
`/var/tmp/subtree-caller-*.log` and `/var/tmp/subtree-recursive-statements.json`.
The diagnostic driver is temporary and reuses the source-control router; it is
not a committed interpreter or parser. The unchanged source retains the pinned
regeneration and thirteen ordered Rust tests recorded at `6137120`.

Next interpret actual loan activity/endings, beginning with the cache-hit local
6 witness, while preserving the existing source semantics and initialized
storage accounting. Then discharge universal native input readiness, budgets,
physical success, exclusive temporary/argument/output owner transfer and dynamic
parsed-region/destructor composition. Reuse the completed recursive dispatcher,
whole-run caller retention, source/native/type/binder/helper/control/entry and
cleanup proofs instead of repeating them. Public maximum/cold-table teardown,
separate wrappers/input policy, W04 D1-D4, remaining MEM-03/W05 and MEM-04/global
resources/G3, and all other LV/Droschinsky mathematical/software/release/
application obligations remain part of the active full goal.
