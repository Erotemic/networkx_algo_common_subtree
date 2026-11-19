# Successful-left payload and actual right-query concatenation

Baseline: `d69958c`, branch `Droschinsky-algos`. This increment continues
SRC-01/W06-C3 on the unchanged parsed evaluator. It constructs the first fifteen
instructions of the successful-left/right-contraction region. Full evaluator
totality and production resource bounds remain open.

## Checked endpoints

`SourceEval.Evaluator.entry_pair_right_prefix_complete` in
[`SourcePairRightPrefixEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightPrefixEntry.lean)
constructs execution from parsed evaluator entry through thirteen stable actual
prefix checkpoints. It retains the previous full sixty-instruction matched/left
prefix and exact-cost left call, and appends the actual fifteen-instruction
right-region prefix. Every larger common helper fuel/budget pair reaches the
same worlds and activations.

The explicit recursive premises remain universal `NativeTotal` for the smaller
head, tail and left-contraction requests. Independent native head/tail success,
checked subtotal/root addition, and native left success equations select this
successful branch. The native left equation is compared with the result
actually constructed by the preceding endpoint; it is not a successful
physical parent-run or post-frame premise. Arbitrary typed warm tables and
legal original query/table/caller aliases remain supported. Cache soundness
and recursive witness-owner freshness are not assumed.

`pair_right_prefix_complete` in
[`SourcePairRightPrefix.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightPrefix.lean)
composes the following actual instructions, with the unchanged `rightCode 15`
as continuation:

| Indices | Actual behavior |
| --- | --- |
| 0–5 | Open scratch 82, move the `Some` payload from 74 through 82 into existing empty payload 81, drop the emptied scratch, retire 82 and fake-read 81 |
| 6–10 | Open result 85 and reborrow original right child words through 29/30 into 86/87 |
| 11–14 | Execute unchanged concatenation into 85, retire moved roots 87/86 and fake-read the owned result |

`RightConcatScope` exposes the exact native left witness in 81, partial optional
hole in 74, owned left query 71, owned appended right query 85, native table 75,
matched candidate 64, scalar holes/total and original query snapshots. It
records retired scratch/reference roots. Complete ownership and Box coverage
persist. The parsed-entry endpoint proves every parent root at index 88 or
above is still unbound, from actual parent-root change certificates. This is
stack-root freshness, not a recursive witness Box-provenance theorem.

The exact native right append is `OrderedSolver.appendWord rh rt`. Its helper
events are `MemoSource.concatenateEvents rh rt`; its complete call cost is

```lean
(Cost.local (Action.call .concatenate (concatenateArgs 86 87) 85).weight).plus
  (SourceEval.Legacy.costMap nativeCost)
```

This cost identifies the actual concatenation call, not the whole fifteen-
instruction prefix or a production runtime envelope. Original heap bytes at
bound roots other than the intentionally written payload 81 remain unchanged.

The component endpoints are `pair_right_payload_complete`,
`pair_right_concat_arguments_complete`, `pair_right_concat_call_complete` and
`pair_right_concat_scope_complete` in their corresponding `SourcePairRight*`
modules. `contractRight_actions` in `SourcePairRightProgram.lean` checks the
literal 36-instruction source region and actual optional-result continuation.
Only the first fifteen instructions are constructed here.

## Reusable owner transfer

`SourceEval.Addressed.original_move_into_complete` in
[`SourceOriginalMoveInto.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalMoveInto.lean)
constructs a closed native move into an existing empty bound local. It derives
selected source/store permissions from the original-loan machine, preserves
complete ownership/coverage and preserves every other bound root's bytes.

`SourceEval.Evaluator.original_optional_payload_complete` in
[`SourceOriginalOptionalPayload.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalOptionalPayload.lean)
uses it for the generic six-instruction optional-payload pattern. It supports
arbitrary distinct source/scratch/destination indices outside the machine's
loan family, a native `Some` witness, an empty bound destination and an unbound
scratch within the frame. The actual partial move, owner transfer, zero-owner
drop and physical scratch retirement restore exactly the initial root map.
The source becomes the typed partial optional hole and the destination owns
the native witness. No physical post-state is provided as a premise.

## Consumers

Three additional kernel consumers in `Tests/SourceCacheMissSetup.lean`
discharge every smaller recursive contract with proved empty-input totality:

- Repeated table-owned original query aliases derive all thirteen checkpoints,
  the full preceding sixty-instruction prefix, successful optional inspection,
  owned right query and all future roots at index 88 or above unbound.
- A new fourteen-Box warm-table fixture returns a nonempty left witness of
  score seven. Its two owned Boxes actually transfer into 81 beside the
  six-Box matched candidate, with the typed table and original aliases retained.
  This uses arbitrary typed cache contents, without a soundness premise.
- Nonempty right concatenation operands construct a four-Box owned query in
  85 from an external right query and table-owned left query. The native table
  includes the preceding left-contraction insertion and the helper's exact
  native event sequence is exposed. This consumer stops before right recursion;
  it does not assume universal totality for a nonempty pair/pair request.

## Validation and reproduction

The 4,204-job root build and six affected Lean suites pass, including all eight
recursive runtime cases. All 1,859 unique audited endpoints, including ten new
public theorems across nine new proof modules, use only `propext`,
`Classical.choice` and `Quot.sound`. Eight elaborated statement seeds resolve
1,306 unique declarations with zero unknown references. Thirteen ordered Rust
tests and nine Python frontend checks pass. The full 47-suite/native-WP evidence
at `d49f638` is inherited, not rerun. Maintained Rust, generated extraction,
interpreter/parser semantics, dependency pins and shared tooling are unchanged.

From the repository root unless shown:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-right-concat-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_concat_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_concat_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_concat_arguments_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_payload_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_optional_payload_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.original_move_into_complete
```

All seven build caches are guest-ext4 bind mounts. Cargo metadata selects the
mounted standalone-crate target; Cargo/Rustup homes are ext4. Machine-local logs
are `/var/tmp/subtree-right-concat-{build,consumer,expressions,control,helpers,
lifecycle,runtime,axioms,statements,rust,python}.log`; statement data has the
same prefix. Source scanning supplies candidate names; the kernel audit and
elaborated statement query establish the reported endpoints and assumptions.

## Remaining work

Construct right argument/view storage 90–94, original left-query reborrow 91
and fresh views 93/92 into owned word 85. Move the table from 75 into 94,
execute the strictly smaller right recursive request, and construct its real
cleanup/result scope and optional switch. Twenty-one right-region instructions
remain after this increment. Complete both left/right failure/success joins.

Derive recursive witness owner provenance or equivalent selected destructor
loan-disjointness from actual execution for general owned cleanup. Original
query-loan destructor obligations persist independently of fresh word-loan
support and stack-root freshness. Complete overflow exits, choice, insertion,
remaining parent returns and full pair/pair `NativeTotal` induction. Dynamic
parsed regions/destructors, public maximum/cold-table teardown, wrappers/input
policy/resources/G3 and every other planning target remain open. Full SRC-01/C3
and the full user goal remain active.
