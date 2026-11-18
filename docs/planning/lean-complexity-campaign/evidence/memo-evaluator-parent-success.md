# Whole successful pair/pair body and dispatcher

Baseline: `1f0a202` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [finish/closure checkpoint](memo-evaluator-finish-cleanup.md) constructed the
successful-right continuation. This follow-up constructs the entire original
parent body from parsed entry, then checked recursive dispatch and closure.
Four smaller `NativeTotalFresh` contracts and independent native head/tail,
checked-add and left/right success equations select this case. No whole-parent
source execution, parent native equation, desired post-frame or successful close
is an input. Other return paths and universal pair/pair induction remain open.

## Earlier switch inspections

`SourceOptionalPayloadTag.lean` proves `optional_read_node` and
`Calling.Prefix.typed_payload_tag`. A successful payload move or copy implies
the earlier typed optional has tag1. The checked finite prefix supplies actual
validity and typing; closed local preservation reflects its prepared mask back
to the earlier checkpoint. The existing actual scrutinee constructor then
derives its physical inspection. This reflects already constructed finite
instructions, rather than assuming that the whole parent takes a desired path.

`SourceEvaluatorRouteTypes.lean` derives locals52/59 as scalar options from the
existing checked-add action constraints. Generic `Types.call_result_type` reads
ordinary declared call outputs. Types31/41 reuse the preceding checked
call-output/field-move proof. No duplicate local layout, parser or source checker
is introduced.

`SourcePairRouteInspections.lean` derives all four earlier successful optional
inspections: head31 from the tail payload move, tail41 from the subtotal payload
move, subtotal52 from the root-score copy and root59 from the matched-prefix copy.
Actual local typing and call readiness come from the original pinned declaration
certificate throughout.

## Complete original body

`SourceCallingReturnedRouting.lean` proves that a selected returning branch
bypasses its join in the actual calling executor, retaining the inspection cost.
`SourcePairSuccessfulRouting.lean` composes all eight actual prefixes, all
successful inspections and the constructed finish through the original body.
The intermediate word-pair check executes its real `.done` branch and continues
into head recursion. Every actual inspection, instruction and returning branch
cost remains in the resulting full cost; no source branch is deleted.

`SourcePairSuccessfulBody.lean` proves
`entry_pair_successful_body_complete`. Parsed readable inputs, complete
ownership/coverage, legal original aliases, the four smaller fresh contracts and
independent success equations construct the full parent body. The existing
right-result constructor and native entry supply its actual prefixes and initial
typed resource context. Older cleanup masks and physical roots are derived.
The early miss constructor independently supplies lookup and word inspections;
prefix determinism at shared sufficient bounds identifies its real checkpoints.
The new inspection and routing lemmas compose those checkpoints with the complete
finish. The endpoint returns the actual body world, packet, full cost, empty
activation, root separation/freshness, protected caller reads and witness-field
owner bound.

## Checked invocation and stronger totality

`SourceInvokeReturnedPacket.lean` reflects a successful actual invocation into
its body's exact returned packet and actual close. `Storage.close_memory` proves
that successful closure leaves memory bytes intact. These are executor-shape
facts, not new physical-success premises.

`SourceEvaluatorBodyFreshClosure.lean` proves
`evaluator_body_close_total_fresh`. It retains every guarantee of the existing
body-closure constructor, identifies the returned packet through actual invoke
and preserves a separately proved witness-field owner bound. Native/source
agreement, readable output, complete ownership/coverage, caller guards and exact
world/packet/full cost at larger bounds remain exposed.

`SourcePairSuccessfulTotality.lean` proves `pair_successful_native` directly by
unfolding the pinned native function with the independent smaller-call and
checked-add equations. `pair_successful_total_fresh` combines that result with
the constructed body and checked closure to obtain the actual
`Recursive.original` evaluator call. It exports the full native/source evaluation,
readability, well-formedness, protected reads, output/caller/external ownership
and live-Box coverage, returned witness provenance and stable sufficient bounds.
The table may retain old owners; only the witness field receives the fresh bound.
Earlier endpoint statements, induction contracts, independent mathematical
specifications, source semantics, generated artifacts, maintained Rust and pins
are unchanged. This is the successful case of the stronger induction contract,
not a universal instance of it.

## Validation and reproduction

The 4,311-job library build passes. All 2,066 unique audited endpoints, including
thirteen new theorems across nine modules, retain only `propext`,
`Classical.choice` and `Quot.sound`. Eight elaborated statement seeds export
1,346 unique records without unknown references.

All six affected Lean suites pass, including eight recursive runtime cases.
The new whole-parent consumer in `Tests/SourceCacheMissSetup.lean` discharges all
four smaller contracts with proved empty-query fresh instances. It uses the
existing twenty-owner warm table and table-owned query aliases, then constructs
the entire parsed evaluator call through all parent switches, finish, guarded
return and closure. Its output packet has thirty-eight owners, comprising the
six-owner matched witness and thirty-two-owner inserted table. It checks actual
native/source evaluation, complete final ownership/coverage, witness freshness
and exact dispatcher stability at larger bounds. No expected parent execution,
later checkpoint mask/root/storage fact or final frame is supplied. Prior finish,
choice-order/tie and independent six-owner cleanup consumers still pass.
Thirteen ordered Rust tests and nine Python frontend checks freshly pass.

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
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-parent-success-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-parent-success-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_successful_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_successful_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_successful_body_routing \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_successful_route_inspections \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.typed_payload_tag \
  SubtreeProofs.Rust.SourceEval.Types.call_result_type \
  SubtreeProofs.Rust.SourceEval.Evaluator.evaluator_body_close_total_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.invoke_returned_close
```

Evidence logs use `/var/tmp/subtree-parent-success-{build,consumer,output,
branches,control,lifecycle,runtime,axioms,statements,rust,python}.log` plus source/
statement JSON. Accepted intermediate milestones are also recorded in
`/var/tmp/subtree-parent-{payload-tags,route-types,returned-routing,body,
fresh-closure,totality}.log`. Source scans yield candidates; accepted declarations and
elaborated statement/axiom closure establish proof status. All seven build
caches are ext4 bind mounts; Cargo metadata selects the mounted standalone
target and Cargo/Rustup homes are on ext4. Full 47-suite/native-WP evidence at
`d49f638` remains inherited, not a fresh full-suite run.

## Remaining work

Complete the other optional-result joins, overflow/failure exits and parent
returns, including the stronger None-result provenance at existing failure bases.
Then discharge universal pair/pair `NativeTotalFresh` induction. Dynamic
regions/destructors, public maximum and cold-table teardown, wrappers/input
policy/resources/G3 and every other planning requirement remain open. No full
SRC-01/C3 or production resource closure is claimed; the full goal remains active.
