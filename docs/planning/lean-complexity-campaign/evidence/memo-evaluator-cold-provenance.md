# Cold evaluator ownership provenance

Baseline: `f34c3fd` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The universal evaluator already constructs every finite request under the legal
native/caller/external frame model. Its witness-only provenance permits old warm
table owners. This follow-up proves whole-packet freshness for a cold table,
providing the missing provenance basis for the public maximum's table teardown.
Public maximum execution and cleanup remain separate obligations.

## Backward live-Box provenance

`SourceBoxOrigin.lean` defines `BoxOrigin before after`: memory length does not
decrease, and any live output Box below the original heap length was already a
live input Box. The relation composes transitively. Allocation, symbolic stack
entry, helper Box suffixes, writes and retirement preserve it. This is stronger
than forward preservation of old live cells: it excludes resurrection of old
dead Boxes and conversion of old stack identities into Boxes.

`SourceActionBoxOrigin.lean` derives the relation for actual guarded result
stores, assignments, non-call actions and calls with the actual post-argument
suspended stack. `SourceCallingBoxOrigin.lean` propagates it through selected
branches, continuations, early returns, argument storage and checked return
cleanup. `SourceRecursiveBoxOrigin.lean` closes recursive dispatch by fuel
induction, using independent input types to derive actual path readiness.
All eight helpers reuse the existing allocation/owner ledger. The proof does
not replace helpers or assume a desired output allocation interval.

The same module derives preservation of every suspended caller read for a
successful typed recursive run, even when the requested guards are a subset.
Thus complete caller owner identities are retained without requiring stronger
guards at the original evaluator invocation.

## Cold totality and the returned table

`original_fresh_output_of_no_input_owners` combines backward provenance, initial
live-Box coverage, final complete ownership uniqueness and full caller-owner
preservation. Every old live Box already belongs to the retained caller/external
ledger. It cannot also occur in the returned packet. Old dead and non-Box cells
are excluded by backward provenance. Consequently every returned owner lies at
or beyond the original heap length.

`native_evaluate_cold_total` composes this fact with universal evaluator totality
for arbitrary finite native query pairs and canonical empty table input. It
constructs joint sufficient fuel/readback bounds, actual checked execution,
native result and updated table, pure `Evaluation` at the same complete cost,
readable output, well-formed final memory, all caller reads, complete output/
caller/external ownership and coverage, and whole-packet freshness. Every larger
sufficient pair of bounds returns the identical world, packet and cost. No
child contract, parent success, fresh-table postcondition, cache soundness or
input-width bound is a premise. Mathematical consistency still uses the
independent sound-cache/input-width hypotheses of the preceding endpoint.

`SourceMaximumBody.lean` gives a reviewable 17-instruction body with kernel
identity to the actual parsed source: eight preparation instructions, the
evaluator call, and eight cleanup instructions followed by return. Moving the
option from tuple local 3 precedes the explicit table drop. This source identity
does not prove successful maximum execution or its cleanup permissions.

## Validation

The new `Tests/SourceColdProvenance.lean` kernel consumer uses two aliased
references to a three-edge query, seven old external owners, an unrelated old
dead Box and a live scalar stack cell. The whole returned packet is proved to
own only addresses beyond all nine original cells. Separate boundary consumers
reject resurrection and stack-to-Box conversion under `BoxOrigin`. The suite
passes and is registered in ordinary CI.

The 4,349-job library build and eight affected Lean suites pass. All 2,146 unique
audited endpoints retain only `propext`, `Classical.choice` and `Quot.sound`.
The audit includes all 25 new theorems in six proof modules. Eight elaborated
statement seeds export 1,268 unique records with zero unknown references.
Thirteen ordered Rust tests and nine Python frontend checks pass. CI lists
57 Lean suites; this checkpoint freshly runs the eight listed suites, not all
57. The prior fourteen-case `SourceRecursiveExecution` run remains live in its
original process; it is pending and is not counted as a pass. Original thirteen-
case runtime evidence at `c2b4349` and full 47-suite/native-WP evidence at
`d49f638` remain inherited. Maintained Rust, generated output, independent native
and mathematical specifications, and source/toolchain pins are unchanged.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceColdProvenance.lean)
(cd proofs && lake env lean Tests/SourceUniversalFresh.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceOwnerProvenance.lean)
(cd proofs && lake env lean Tests/SourceRecursiveCalls.lean)
(cd proofs && lake env lean Tests/SourceCallingProgram.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo metadata --locked --no-deps --format-version 1 \
  --manifest-path rust/crates/verified_ordered_core/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-cold-provenance-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-cold-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_evaluate_cold_total \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_fresh_output_of_no_input_owners \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_boxOrigin \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_callers_preserved \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.BoxOrigin.fresh_output \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.invoke_boxOrigin \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_evaluate_total_fresh \
  SubtreeProofs.Rust.SourceEval.Maximum.actual_body
```

Logs use `/var/tmp/subtree-cold-provenance-{build,library,consumer,axioms,
statements,rust,python}.log` and individual suite names for the eight regression
logs, plus the source/statement JSON. The initial direct builds additionally use
`/var/tmp/subtree-{box-origin,action-box-origin,calling-box-origin,
recursive-box-origin}-build.log`. Earlier failed drafts are superseded by the
accepted library build. All seven caches are checked ext4 bind mounts. Cargo
metadata selects the mounted standalone crate target; Cargo/Rustup homes are on
local ext4. Before resuming or restarting the pending runtime suite, inspect
`/var/tmp/subtree-universal-fresh-runtime-state.json`, its actual session/process
and log. Preserve the original process while live.

## Remaining scope

Construct the actual public maximum entry, eight preparation actions, evaluator
call, eight cleanup actions and return/close with exact complete costs. Reuse
whole-packet cold provenance to derive table drop permission through the actual
partial-local field transfer; retain allowed shared aliases. Do not supply a
desired maximum success or cleanup frame as an input.
Dynamic parsed-region/destructor-instance interpretation, wrappers/input policy,
G3 adversaries, W04/MEM-03/W05/MEM-04 resources, representations/global time/space,
APP and all other planning requirements remain. Logical retirement is not a
physical allocator/free-cost or peak-space theorem. The D12 source-operation
boundary, Charon/Aeneas import, runtime/compiler/physical allocator assumptions
and IEEE-754 exclusion remain unchanged. No full SRC-01/C3 or production resource
closure is claimed; the full goal stays active.
