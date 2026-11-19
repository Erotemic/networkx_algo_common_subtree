# Successful-right cleanup, return and frame closure

Baseline: `49eb405` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [parsed return-storage checkpoint](memo-evaluator-return-storage.md)
constructed the first fifty-six finish instructions. This follow-up derives
the missing older masks and physical root presence, constructs all remaining
forty-one instructions, then the checked return and call-frame closure.
The complete successful-right finish continuation has finite sufficient bounds
and retains its exact world, packet and full source cost at larger bounds.
It does not yet compose all earlier switches into a whole parent body or close
general pair/pair induction.

## Root presence and older masks

`SourceRootPresence.lean` proves exact storage-presence transitions for actual
instructions, including calls, and for actual finite prefixes. Only storage-live
and storage-dead change presence. A finite slot-list interpretation supports
kernel-checked evaluation without assuming bindings or choosing their addresses.
Actual `enter` determines initial argument presence.

`SourcePairRootPresence.lean` applies these facts to the eight actual prefixes
and `finishActions.take 56`. The twenty-six bound locals are exactly
`[0,1,2,3,13,27,28,29,30,31,32,37,41,42,47,51,58,64,71,74,75,81,85,88,89,95]`.
Empty logical masks still retain their physical roots.

`SourcePrefixMaskFacts.lean` reflects successful source moves/copies through
typed actual prefixes. Whole-local moves leave empty masks; moving the payload
of a typed optional embedding leaves the one-field constructor hole; a
successful whole-local copy establishes zero owned descendants. Untouched
prefixes preserve owned-cell counts, including when reference preparation ends
a shared mask.

`SourceEvaluatorCleanupTypes.lean` derives the types of locals 31 and 41 from
the existing evaluator call-output and field-move action constraints. It supplies
no duplicate local layout or parser. `SourcePairOlderMasks.lean` derives empty
table masks 3/32, optional payload holes 31/41 and the zero-owner scalar mask 51
from the existing actual head/tail/score/root prefixes, then retains them through
both contractions and output assembly. Earlier endpoint statements, smaller
`NativeTotalFresh` contracts, independent hypotheses and source semantics remain
unchanged.

## Constructive mixed retirement

`SourceRetirementPresence.lean` constructs a real `RetirementPlan` from checked
storage presence. `SourceFreshRetirement.lean` proves
`RetirementPlan.complete_fresh`. Each drop uses the existing semantic fresh-owner
permission; each storage-dead checks zero owned descendants after preceding
drops. Preparation preserves the box counts used by that check. Complete native
ownership, caller ownership, live-Box coverage, original loan origins and exact
memory bytes survive. Old query/table/caller aliases remain legal. This is
symbolic retirement, not a physical allocator or peak-space theorem.

`SourcePairFinishCleanup.lean` constructs all forty-one remaining finish
instructions, including both owned-query drops at 85/71, older constructor holes,
scalars, tuple and original parameters. Only return root 0 remains bound; every
other local is empty. Its result witness-field bound survives, while the inserted
table may retain arbitrary old owners.

`SourcePairFinishReturn.lean` constructs the actual guarded return move with
complete readable packet/footprint/frame/coverage evidence and returned witness
provenance. `SourcePairFinishComplete.lean` composes all ninety-seven finish
instructions and return, exporting stable finite fuel/budget bounds.
`SourcePairFinishClosure.lean` then constructs actual checked frame closure from
original caller guards, ownership and closed output typing. All remaining stack
roots retire; output ownership, coverage, readability and protected caller reads
survive. No successful close or desired final world is supplied as a premise.

## Validation

The library build passes with 4,302 jobs. The maintained audit accepts all 2,053
unique endpoints, including thirty-three new theorems across eleven modules,
with only `propext`, `Classical.choice` and `Quot.sound`. Eight elaborated statement
seeds export 1,161 unique records with no unknown references.

All six affected Lean suites pass, including eight recursive runtime cases.
The parsed-entry fixture retains twenty old table owners and table-owned query
aliases, and discharges all four smaller fresh contracts with proved empty-query
instances. Its actual eight prefixes derive older masks and exact root presence.
It constructs the complete finish continuation and checked frame closure with
stable sufficient bounds, and checks the readable thirty-eight-owner output:
six witness owners plus the thirty-two-owner inserted table. A second consumer
constructs all remaining cleanup and the checked return directly from its parsed
instruction-56 checkpoint. Neither consumer assumes later root/mask/storage
facts, an expected final frame, a parent execution or successful closure.

The affected regression commands are:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-finish-cleanup-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-finish-cleanup-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_closed_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_return_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_cleanup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_older_masks \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_root_presence \
  SubtreeProofs.Rust.SourceEval.Addressed.RetirementPlan.complete_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.typed_optional_hole
```

The independent positive-drop fixture constructs retirement of a six-owner local
while retaining nested query aliases into two old table owners. A kernel-checked
observation of the actual executor confirms all six descendants retired, both
old table owners live and the selected stack root absent. Thirteen ordered Rust
tests and nine Python frontend checks pass. All seven build caches are verified
ext4 bind mounts; Cargo metadata selects the mounted standalone target and both
Cargo/Rustup homes are on ext4. Generated artifacts, maintained Rust and pins are
unchanged. Full 47-suite/native-WP evidence at `d49f638` remains inherited.

Machine-local evidence uses `/var/tmp/subtree-finish-cleanup-{build,axioms,
statements,branches,control,lifecycle,runtime,rust,python}.log`, source/statement
JSON, `/var/tmp/subtree-cleanup-{parsed,positive}-consumer.log` and the individual
root/mask/retirement/finish module logs. The shared submodule supplies source
scanning and `leanq statement`; scans are candidates, not proof-status evidence.

## Remaining work

Compose the constructed finish/closure with the earlier actual pair/pair switch
routing and parsed entry to obtain whole successful-parent body/dispatcher
endpoints and returned witness provenance. Complete both optional joins,
overflow/failure exits, remaining parent returns and universal pair/pair
`NativeTotalFresh` induction. Dynamic regions/destructors, public maximum and
cold-table teardown, wrappers/input policy/resources/G3 and every other planning
requirement remain open. No full SRC-01/C3 or production resource closure is
claimed; the full goal remains active.
