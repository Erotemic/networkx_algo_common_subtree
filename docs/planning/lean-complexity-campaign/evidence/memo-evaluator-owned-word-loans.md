# Constructed fresh word views with precise loan anchors

Date: 2026-11-18. Baseline: `8c1219d` on `Droschinsky-algos`.
Nine new modules provide thirty-two public checked theorems. Parsed evaluator
entry reaches the fresh left contraction references through nine stable actual
prefix boundaries. The new construction executes instructions 39–43 of the
sixty-instruction `contractLeft` prefix. The right recursive argument, table
argument and contraction call itself remain open.

## Checked source endpoints

`SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_word_views_complete`
in [`SourcePairLeftWordViewsEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftWordViewsEntry.lean)
takes the same independent readable inputs, complete input/caller/external owner
resources, parent cache miss, smaller-head/tail `NativeTotal` contracts and
native head/tail/subtotal/root success equations as the preceding concatenation
checkpoint. It constructs parsed entry and all nine common/miss/head/tail/
subtotal/root-score/matched/concatenation/fresh-view prefix boundaries at shared
sufficient helper bounds. The final machine retains the matched candidate,
updated table, total, all seven original query/view snapshots, the owned native
appended word in 71, two actual shared views in 78/77, fresh empty bound result
storage 76 and unbound future slots 74/75/79/80/81. No totality premise for the
left contraction request is needed to construct these five setup instructions.
No successful physical parent run, cache soundness, recursive witness freshness
or global alias ban is supplied.

`pair_left_word_views_complete` in
[`SourcePairLeftWordViews.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftWordViews.lean)
constructs the actual five instructions from an existing owned concatenation
checkpoint: open 76, open 77, open 78, borrow local 71 into 78, then reborrow its
referent into 77. The owned word stays in 71 throughout. The actual continuation
determines reference preparation at each instruction. Complete native ownership,
original loan origins, exact word/view masks, activation count/frame, untouched
roots and old bound-root bytes are retained. The result-storage root's raw cell
remains the actual uninitialized empty tuple.

The carried native concatenation event profile and complete concatenation call
cost remain the preceding checkpoint's helper-call cost. This increment does
not identify a complete nine-prefix or parent-invocation cost.

## Original and freshly anchored loans

`LoanSupport` in
[`SourceLoanSupport.lean`](../../../../proofs/SubtreeProofs/Rust/SourceLoanSupport.lean)
is an actual represented local-resource inventory whose loans satisfy a supplied
address predicate. Canonical inventory uniqueness identifies that support for
any representation of the same local. It transports across preparation,
clearing, allocation and preserved reads. `LocalResources.borrow_source`
constructs the actual borrow graph with every new loan inside the starting
local's concrete read footprint, including its stack root. It does not discard
that root by treating a fresh owned-word borrow as an original-data reborrow.

[`SourceOwnedLoanAnchors.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOwnedLoanAnchors.lean)
proves a closed owning local's read footprint consists only of its Box owners
and its own stack root. Owner classification and distinct valid roots exclude
every other selected stack root. Given independent owner disjointness, the same
read footprint excludes another selected owner set. These facts retain aliases
into the anchored word's owned Boxes; no global owner/loan separation is assumed.

`AnchoredLoanMachine` in
[`SourceAnchoredLoanMachine.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchoredLoanMachine.lean)
keeps the original family under the unchanged pre-entry loan bound, and a
separate fresh family supported by the precise read footprint of a current
closed owning word local. The word's actual local inventory, native value and
local-count bound remain part of the invariant. Prefix preparation preserves
both families. `rootLoans` derives selected store/retirement loan permissions
for roots other than the anchored word's root. `move_local` derives selected
actual local-move permissions, including owned-valued locals whose raw cells
are neither uninitialized nor shared-pointer cells. Neither theorem supplies
permission to move or destroy the anchored word while its views are live.

[`SourceAnchoredBorrow.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchoredBorrow.lean)
constructs checked native-reference assignments, extending the fresh family
while transporting the actual owning anchor, older fresh supports and stricter
original origins. [`SourceAnchoredStorage.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchoredStorage.lean)
preserves the invariant across actual unrelated storage opening.
[`SourceSupportedReborrow.lean`](../../../../proofs/SubtreeProofs/Rust/SourceSupportedReborrow.lean)
proves that a reborrow crossing an existing supported shared reference stays
inside its loans, excluding the intermediate reference's own stack root.

`other_owners_avoid_anchor` in
[`SourceAnchorOwnerPermissions.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchorOwnerPermissions.lean)
derives disjointness between the precise anchor read footprint and another
local's owners from complete owner uniqueness and the actual remaining-local
inventory. Thus fresh word views add no loan conflict with those separate
owners. Original-query loans still require their independent selected owned-
destruction permissions; this is not a complete general destructor theorem.

## Consumers

Two new kernel consumers in `Tests/SourceCacheMissSetup.lean` discharge both
smaller recursive contracts using proved empty-input totality. The first
repeats the same table-owned query pointer, derives all nine stable prefix
boundaries and obtains actual result-root loan permission while both fresh word
views are live. The second constructs a four-Box concatenated word from a
larger external left query and a table-owned right query, retains all exact
original query snapshots and both fresh native views, and derives exclusion of
the separate matched candidate's owners from the fresh-loan anchor. Neither
consumer assumes cache soundness or completed physical invocation success.

## Validation and reproduction

The 4,177-job root build and six affected Lean suites pass, including all eight
recursive runtime cases. All 1,820 unique audited endpoints, including the
thirty-two new public theorems, use only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds resolve 1,293 unique declarations
with zero unknown references. Thirteen ordered Rust tests and nine standalone
Python frontend checks pass. The broader 47-suite/native-WP evidence at
`d49f638` is inherited, not rerun. No maintained Rust, generated extraction,
parser, interpreter semantics, shared-tooling or dependency-pin changes occur.

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
  --out /var/tmp/subtree-word-loans-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_word_views_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_word_views_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.AnchoredLoanMachine.assign_owned_view \
  SubtreeProofs.Rust.SourceEval.Addressed.AnchoredLoanMachine.assign_supported_view \
  SubtreeProofs.Rust.SourceEval.Addressed.AnchoredLoanMachine.move_local \
  SubtreeProofs.Rust.SourceEval.Addressed.AnchoredLoanMachine.rootLoans \
  SubtreeProofs.Rust.SourceEval.Addressed.AnchoredLoanMachine.other_owners_avoid_anchor \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.LocalResources.borrow_source
```

All seven caches remain guest-ext4 bind mounts. Cargo metadata selects the
mounted standalone-crate target and Cargo/Rustup homes are ext4. Machine-local
logs are `/var/tmp/subtree-word-loans-{build,consumer,expressions,control,helpers,
lifecycle,runtime,axioms,statements,rust,python}.log`; statement data uses the
same prefix. The theorem scanner supplied candidate names only; the kernel
axiom audit and elaborated statement query validate the reported endpoints.

## Remaining work

Construct right argument 79 and moved table argument 80, then execute the
strictly smaller left contraction request using its universal recursive
contract. Preserve the anchored machine through the actual call, extract its
result/table, retire argument roots and end reference 78 at the actual source
point. After fresh references end, narrow back to the strictly original loan
family. Complete the left failure/success joins and the right contraction path.

Derive recursive witness owner provenance or equivalent selected destructor
loan-disjointness from actual source execution for general owned cleanup;
original-data query loans remain a separate obligation from fresh word loans.
Complete overflow exits, choice, insertion, remaining parent return/closure and
full pair/pair `NativeTotal` induction. Dynamic parsed regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and every
other planning target remain open. Full SRC-01/C3 and the full goal stay active;
this increment establishes no production resource closure.
