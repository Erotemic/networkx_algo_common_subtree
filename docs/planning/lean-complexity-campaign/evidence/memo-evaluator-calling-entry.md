# Calling control, parsed entry and checked return cleanup

Baseline: `6055cff` on `Droschinsky-algos`. This continues W06-C3/SRC-01;
C3 and the full planning goal remain open. Production Rust, generated source,
toolchain pins and the independent mathematical/source specifications are
unchanged.

## Actual caller stack and control

`SourceEval.Addressed.Derived.Callees` now receives the actual suspended
activations as well as protected addresses. `Derived.call` evaluates arguments
once, then passes the post-argument activation followed by the original caller
list. Its existing `call_spec` derives validity of that full stack from operand
execution. `CallsRespect` explicitly accepts those valid suspended activations;
`Helpers.callee_respects` is adapted without changing helper execution, native
shape/fuel premises or original source costs. Ordinary helpers retain their
existing heap/borrow/region contracts and insertion's transferred owner ledger.

`SourceEvalCallingControl.lean`, namespace `SourceEval.Addressed.Calling`, uses
`Control.execWith` with the checked call instruction and existing non-call,
scrutinee and return primitives. It reuses source routing, switch costs and early
returns; it does not introduce a second control interpreter. Public endpoints:

- `readyFor_noCalls`: every call-free body has input readiness for any callee.
- `Step.callers`, `noncall_spec`, `instruction_spec`: successful call/non-call
  instructions agree with the original source action/full cost and preserve
  frame/count, active/world validity and exact suspended resource inventories.
- `exec_done`, `exec_ret`, `exec_step`, `exec_switch`: executable equations.
- `selected_spec`, `selected_simulation`: only the selected supported arm needs
  its input-side domain condition; unsupported routing still fails.
- `exec_spec`: successful calling-control execution agrees with the complete
  source outcome and cost and retains active/caller/returned-packet validity.

`ReadyAt` concerns the actual evaluated argument packets. `ReadyFor` composes
that independent input-shape/fuel condition along the selected concrete path,
after actual preceding instructions and before a reached continuation. Early
return imposes no readiness obligation on a skipped join. It contains no desired
source result or desired post-argument context. The theorem still needs both
this readiness evidence and actual concrete success; neither is claimed for all
113-local evaluator paths yet. The earlier non-call `Derived.exec` remains a
compatible foundation; `Calling.exec` is the executor that supports calls.

## Checked stack cleanup

`SourceActivationClose.lean`, namespace
`LookupSource.Partial.Addressed.Storage`, enumerates all present roots within
the activation's declared bound. It checks the actual active/caller scans, zero
remaining owner occurrences, returned graph liveness and disjointness of every
remaining stack root from external guards, caller reads and the complete output
read graph. It then logically retires exactly those stack roots.

Public endpoints:

- `Activation.mem_stackAddresses`, `binding_mem`, `stack_class`: enumeration
  covers every bounded binding and has the correct actual stack class/liveness.
- `Scanned.zero_boxes`: an empty computed owner ledger implies every remaining
  source local has zero destructor Box count, including out-of-bound empty slots.
- `close_spec`: valid active/caller frames and a readable incoming returned
  packet, plus successful cleanup, derive retirement of every remaining binding,
  zero remaining source owner counts, unchanged memory/classes and Box liveness,
  world well-formedness, live output readback, retained external guards and exact
  suspended caller inventories/read preservation.
- `close_complete`: independent zero-owner, live-output and root-disjointness
  hypotheses suffice for cleanup success.

The readable input packet comes from the completed return/control proof. It is
not an assumed post-cleanup answer. The output guard covers transitive shared
and owned reads, so a returned reference into any remaining callee root fails.
An unrelated still-owned Box also fails cleanup instead of disappearing.
This closes symbolic remaining stack bindings; it does not establish exclusive
ownership across all temporary packets or interpret all parsed dynamic regions.
It does not prove a physical allocator/compiler cleanup theorem.

## Parsed declaration entry and native choice

`SourceEvalCallingEntry.lean` uses the existing `TypeReader.Definition`, checks
actual arity, constructs fresh argument stack storage with the parsed local
count, runs calling control, requires a return, and performs checked cleanup.

- `Calling.invoke_spec` derives complete source-body execution, original entry
  plus body cost, readable output/world/caller validity and all cleanup facts.
  Input readiness is stated on the derived initial frame, not an arbitrary
  desired body result.
- `Calling.invoke_run` composes the source run equation for an ordinary parsed
  body and its verified callee contract, preserving the entire return cost.
  Box and checked-add continue through the completed intrinsic backend.

`SourceEvalCallingChoice.lean` reuses the already proved native tie rule and
actual choice body. `Choice.invoking_refines` instantiates all input readiness
from its call-free body. A successful invocation returns
`encodeResult (OrderedSolver.selectResult first second)` at exactly
`Choice.cost first second` and closes all remaining callee bindings. It retains
source hypotheses and the explicit concrete-success premise.

`SourceEvalCallingCertificate.lean` accesses the existing checked typed source
reader; it does not construct a substitute declaration. `originalProgram_read`
records the actual read, `choice_fields` checks the selected declaration's
function/count/body, and `originalChoice_spec` exposes the pinned actual
six-local choice declaration for runtime/proof consumers.

These entry points are not yet a recursive program dispatcher. Connecting
choice/evaluator/maximum into that dispatcher still needs the recursive callee
contract, whole-run retained-byte/resource composition, input readiness and all
physical check success. Per-instruction exact suspended resources and valid
callers are not a substitute for the recursive contract's complete `Preserves`
obligation on every protected caller address.

## Consumers and validation

`Tests/SourceCallingProgram.lean` exercises moved numeric call arguments, checked
addition, a retained optional tag after payload movement and early return. The
selected branch returns 42 at 13 source steps while an unsupported evaluator call
in the other arm and an invalid join are skipped. Its domain proof derives the
actual packets and needs no readiness for either skipped path. A callee observer
checks that both actual suspended activations arrive, with the argument masks
already moved. The complete source outcome/cost and validity come from
`Calling.exec_spec` and the existing helper callee contract.

Cleanup then retires all four remaining callee roots while preserving the old
caller's numeric root and output. Adversaries reject a scalar reference escaping
into callee storage, an externally protected callee root and leftover Box owners.
Choice consumers exercise losing-Box retirement, retained winning owner
identities, ties and complete entry/body costs, with all remaining stack roots
dead afterward. A concrete consumer uses `CallingCertificate.originalChoice`.

The full 3,951-job public build and all 41 maintained Lean suites pass, together
with native WP and nine Python tests. The new focused suite and maintained
modules have no diagnostics; existing unrelated root-build warnings remain.
`BaselineAudit.lean` audits 1,030 distinct endpoints, including all 23 new public
theorems, using only `propext`, `Classical.choice` and `Quot.sound`. Shared
`leanq` exports 1,124 unique elaborated declaration statements from five seeds
with zero unknown references. Inspected signatures retain the local callee
contract, selected-path input readiness and physical success; cleanup takes its
readable packet from the preceding checked return, and actual declaration
access has no substitute-declaration hypothesis.

Reproduce after preparing VM caches, from the repository root:

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceCallingProgram.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Run all maintained Lean suites listed in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-calling-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_spec \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.close_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.invoke_run \
  SubtreeProofs.Rust.SourceEval.Choice.invoking_refines \
  SubtreeProofs.Rust.SourceEval.CallingCertificate.originalChoice_spec
```

Temporary machine-local logs use `/var/tmp/subtree-calling-*.log`; they are not
committed dependencies. The unchanged Rust/generated source retains the pinned
regeneration and thirteen ordered Rust tests recorded at `6137120`.

## Remaining full-scope work

Compose the actual recursive program dispatcher over parsed declarations and
these checked call/control/entry/cleanup endpoints. Serve choice/evaluator/
maximum without repeating completed helper, snapshot/native, type/binder,
initial-frame or graph/store proofs. Derive all branch readiness, source/ghost
budgets, complete actual caller/resource preservation and physical success.
Preserve insertion's existing owner transfer and allowed shared aliases.

Complete exclusive temporary/argument/output owner transfer and dynamic parsed
region/destructor interpretation. Then finish public maximum/cold-table teardown,
separate wrappers/input policy, W04 D1-D4, remaining MEM-03/W05 and MEM-04/global
resources/G3. D12 retains the explicit source-operation boundary; source counts
are not production time or physical allocator space. The other LV/Droschinsky
mathematical, software, release and application obligations in the main plans
remain part of the active goal.
