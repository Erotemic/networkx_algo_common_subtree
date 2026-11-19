# Universal checked public maximum and table teardown

Baseline: `cce8f7f` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
This follow-up constructs the complete public `maximum_common_embedding`
execution under the existing addressed source interpretation. It composes the
universal evaluator with actual seven-local entry, all 17 parsed instructions,
the updated table's owned destruction, return and checked stack close. No child
calling contract, successful parent execution, desired post-frame or successful
table drop is a premise of the public endpoint. Dynamic parsed-region and
destructor-instance interpretation remain separate C3 obligations.

## Actual public entry and preparation

`SourceMaximumEntryCertificate.lean` checks the exact typed parsed declaration:
function, seven locals, complete certified body and actual recursive lookup.
`SourceMaximumEntry.lean` constructs its argument storage from readable shared
query packets and the complete retained caller/external owner frame. Shared
arguments own no cells. Both queries may alias each other or retained owners;
their loan footprints originate below the original heap length.

`SourceMaximumPreparation.lean` constructs all eight actual preparation actions:
open return/result storage, reborrow queries into locals 4 and 5, and initialize
the canonical empty table in local 6. The continuation-aware executor decides
reference preparation. Original loan origins, empty result/return bytes, root
identities, complete resources and exact native argument masks persist.

## Evaluator call, result transfer and table destruction

`SourceMaximumCall.lean` constructs the actual evaluator call from locals 4/5/6
into local 3 using proved universal `native_total`. Independent actual argument
types derive readiness. The argument packet owns no cells; cold provenance
therefore proves freshness of the complete returned tuple, including its table.

`SourceColdCallProvenance.lean` is the reusable call/store bridge. It retains the
actual post-argument suspended stack and complete owner partition, derives cold
output freshness through real recursive execution, and preserves the exact
output owner list through guarded storage. Other active locals may own old
Boxes: they remain in the real suspended caller ledger. No global alias ban or
desired fresh allocation interval is substituted for the execution proof.

`SourceMoveAssignmentProvenance.lean` proves that actual operand execution and
guarded assignment retain the remaining owners at every other local, including
a source whose partial mask changed. `SourceMaximumResultTransfer.lean` uses
this to move the option from tuple local 3 into the already-open return local 0.
The real remaining tuple mask contains the table and an empty option field;
its table owners retain their established freshness bound.

`SourceMaximumCleanup.lean` constructs all eight cleanup actions and return:
retire moved argument locals 6/5/4, transfer the option, destroy the remaining
tuple/table at local 3, and retire locals 3/2/1. The table drop's physical guard
follows from fresh table ownership and original bounded loans. Its real owner
list is retired; the existing source destruction traversal and cost are retained.
Return is derived only after all other local masks are empty. Query references
may still alias retained caller data throughout these operations.

## Public endpoints and mathematical claim

`SourceMaximumExecution.lean` composes actual entry, preparation, evaluator call,
table cleanup and return. `SourceMaximumClosure.lean` derives the final stack
close from output typing, complete owner separation and old caller-read bounds,
then lifts the constructed body through the actual parsed recursive dispatcher.

`SourceMaximumTotality.native_maximum_total_fresh` constructs sufficient joint
fuel/readback bounds for arbitrary finite native query words under the legal
native/caller/external frame model. It returns actual native optional value,
matching pure source execution at the same complete cost, readable output,
well-formed final memory, every retained caller read, complete owner uniqueness/
classification/liveness and full live-Box coverage, and fresh output owners.
Every larger sufficient fuel/budget pair returns the identical world, packet and
cost, with matching pure source execution at that fuel. Width bounds are not
execution premises; native overflow/None behavior is retained.

`native_maximum_total_correct` separately adds both independent query semilength
bounds below 2^32. The existing independent mathematical refinement identifies
the returned Some witness as a maximum common ordered tree with an exact edge
score. It retains all physical/source/cost/resource/freshness/stability results.
No reference algorithm's complexity is used as a production complexity proof.

## Validation

The 4,360-job library build and eleven affected Lean suites pass. The two new
suites are registered in ordinary verification CI:

- `SourceMaximumTotality`: kernel consumer with two aliased references to one
  three-edge query, seven old external owners, an unrelated old dead Box and a
  live scalar stack cell. It obtains the independent optimum/exact score and
  complete output resources; every returned owner lies beyond the entire old
  nine-cell heap. No smaller calling contract or parent success is supplied.
- `SourceMaximumExecution`: actual one-edge public maximum with both queries
  aliasing the first caller-owned tree. It checks 2,704 complete source steps,
  five solver calls, full source/addressed value and cost equality, all retained
  caller bytes/liveness, exactly two fresh result Boxes, complete owner coverage,
  and retirement of every discarded table owner and new stack cell.

All 2,163 unique audited endpoints, including the 17 new theorems in eleven proof
modules, retain only `propext`, `Classical.choice` and `Quot.sound`. Eight statement
seeds export 1,311 unique records with zero unknown references. Thirteen ordered
Rust tests and nine Python frontend checks pass. CI lists 59 Lean suites; this
checkpoint freshly runs the eleven listed below, not all 59. The separate
fourteen-case `SourceRecursiveExecution` run remains live in its original
process; pending is not a pass. Original thirteen-case runtime evidence at
`c2b4349` and full 47-suite/native-WP evidence at `d49f638` remain inherited.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceMaximumTotality.lean)
(cd proofs && lake env lean Tests/SourceMaximumExecution.lean)
(cd proofs && lake env lean Tests/SourceColdProvenance.lean)
(cd proofs && lake env lean Tests/SourceUniversalFresh.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceOwnerProvenance.lean)
(cd proofs && lake env lean Tests/SourceRecursiveCalls.lean)
(cd proofs && lake env lean Tests/SourceCallingProgram.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo metadata --locked --no-deps --format-version 1 \
  --manifest-path rust/crates/verified_ordered_core/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-maximum-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-maximum-statements.json \
  SubtreeProofs.Rust.SourceEval.Maximum.native_maximum_total_correct \
  SubtreeProofs.Rust.SourceEval.Maximum.native_maximum_total_fresh \
  SubtreeProofs.Rust.SourceEval.Maximum.body_close_total \
  SubtreeProofs.Rust.SourceEval.Maximum.entry_body_complete \
  SubtreeProofs.Rust.SourceEval.Maximum.cleanup_complete \
  SubtreeProofs.Rust.SourceEval.Maximum.result_transfer_complete \
  SubtreeProofs.Rust.SourceEval.Maximum.evaluate_call_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.original_call_fresh_output_of_no_input_owners
```

Logs use `/var/tmp/subtree-maximum-{entry-build,preparation-build,call-build,
transfer-build,cleanup-build,execution-build,closure-build,totality-build,library,
consumer,runtime,axioms,statements,rust,python}.log`, plus individual suite names
for the nine prior regression logs, and source/statement JSON. The reusable cold
call bridge's direct build uses `/var/tmp/subtree-cold-call-build.log`. Earlier
failed drafts are superseded by the accepted library build and suites.
All seven caches are checked ext4 bind mounts; Cargo metadata selects the
mounted standalone target and Cargo/Rustup homes remain on local ext4. Inspect
`/var/tmp/subtree-universal-fresh-runtime-state.json` and its actual process/
session before any restart of the original pending fourteen-case suite.

## Remaining work and interpretation boundary

Universal evaluator and public maximum execution/table teardown are now proved
under the existing addressed native frame model and D12 source-operation
interpretation. Compose actual dynamic parsed-region and destructor-instance
interpretation, including source-path permissions, escape checks and scalar/
nonowning stack-root protection. Logical owner retirement and source destruction
visits do not establish physical allocator/free time or peak space. Charon/Aeneas
import, primitive/runtime/provenance, mutable/unwind, compiler and physical
allocator boundaries remain explicit. Maintained Rust, generated artifacts,
independent mathematical/native specifications and pins are unchanged.
Indexed/token/reconstruction wrappers, input/error policy, G3 adversaries,
W04/MEM-03/W05/MEM-04 resources, representations/global time/space, APP and all
other planning requirements remain. No full SRC-01/C3 or production resource
closure is claimed; the full goal stays active. IEEE-754 correctness remains
excluded from the initial scope.
