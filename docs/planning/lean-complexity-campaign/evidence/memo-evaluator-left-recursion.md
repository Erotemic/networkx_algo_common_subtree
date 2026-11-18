# Constructed actual left contraction call

Date: 2026-11-18. Baseline: `5424003` on `Droschinsky-algos`.
Eight new modules provide thirteen public checked theorems. Parsed evaluator
entry reaches the actual left contraction return through eleven stable actual
prefix boundaries. The new construction executes instructions 44–48 of the
sixty-instruction `contractLeft` prefix: right-query reborrow, owned-table move
and real recursive evaluator call. Argument/result cleanup and both left-result
branches remain open.

## Checked endpoints and recursive premises

`SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_call_complete` in
[`SourcePairLeftCallEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftCallEntry.lean)
takes independent native readable inputs, complete input/caller/external owner
resources, a parent cache miss, smaller-head/tail `NativeTotal` contracts,
independent native head/tail/subtotal/root success equations and the additional
universal `NativeTotal (OrderedSolver.appendWord lh lt) (.Pair rh rt)` contract.
The latter request strictly decreases the already checked sum of independent
Dyck-word semilengths; no global pair/pair totality instance is supplied.

The theorem constructs parsed entry, all eleven common/miss/head/tail/subtotal/
root-score/matched/concatenation/fresh-view/argument/call prefix boundaries and
one exact recursive call at every larger shared fuel/readback bound pair. Its
actual final world, activation, native optional result, updated table and call
cost are fixed across those bounds. The actual `.evaluate` call and its exact
cost remain exposed at the retained argument checkpoint. No successful
physical parent run, expected post-callee frame, expected left native result,
cache soundness, recursive witness owner freshness or global alias ban is an
input. This establishes a prefix and recursive return, not the parent return.

The result is the actual native `encodeOutput result output` in 76. The table
moved out of 42 and through argument 80; 42 and moved argument masks 77/79/80
are empty. The final complete owner/coverage machine retains all seven exact
original native query/view snapshots, the owned concatenated word in 71 and the
matched candidate, scalar-only old witness masks and root total. Original query
origins keep their strict pre-entry bound, including new right-query view 79;
fresh views 77/78 keep their separate precise word-anchor support when present.
The actual continuation may end an unobserved reference mask before its later
storage-dead instruction. Its stack binding remains until actual retirement.

`pair_left_call_prefix_complete` in
[`SourcePairLeftCallPrefix.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftCallPrefix.lean)
composes all five new instructions while retaining the argument checkpoint,
actual call/cost and whole five-instruction prefix. `pair_left_call_complete`
in [`SourcePairLeftCall.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftCall.lean)
constructs the actual recursive call from ready native arguments. The smaller
contract supplies source execution; selected physical argument moves, output
store permissions, complete native resources and anchored provenance are
derived. `left_contraction_call_arguments` identifies the exact moved masks.

`pair_left_call_arguments_complete` in
[`SourcePairLeftCallArguments.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftCallArguments.lean)
constructs all four actual argument instructions: open 79 and reborrow the
original right query through 2, then open 80 and move the native table from 42.
The freshly anchored left word view in 77, original queries, matched candidate,
result storage 76 and complete original/fresh loan invariants persist. Older
bound-root bytes are preserved through argument construction; the recursive
call preserves older bound-root bytes except for its explicit destination 76.

The reported cost is the complete actual **left recursive call** cost, including
its dispatch and callee execution. It is not the cost of all eleven prefixes or
a full parent invocation. No whole-parent or production resource closure follows.

## Reusable anchored forward machinery

`AnchoredLoanMachine.advance_call` in
[`SourceAnchoredLoanCalls.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchoredLoanCalls.lean)
retains original bounded loans and precise fresh word support through actual
calls with closed outputs. Moved argument masks may clear family members;
unchanged members retain their canonical represented inventories. The owning
word's complete actual read footprint, including every owned Box descendant,
is preserved by the existing suspended-context contract. No presumed post-call
anchor or frame is supplied.

[`SourceAnchoredAssignments.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchoredAssignments.lean)
constructs closed assignments and original-data reborrows in the presence of
fresh word views. New original reborrows extend only the original family. The
selected write transports the exact owning anchor, older fresh supports and
stricter original origins.
[`SourceAnchoredPrefixes.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchoredPrefixes.lean)
packages actual stack-opening, original-view reborrow and closed-value move
prefixes. Selected source-root permission follows from the anchor's read
partition and complete Box ownership, retaining legal query/table aliases.

`MatchedCandidateScope` in
[`SourceMatchedCandidateScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourceMatchedCandidateScope.lean)
retains the candidate, scalar holes, total and retired construction roots
independently of the table's current location. `MatchedScope.candidate_scope`
projects the existing stronger table-at-42 checkpoint; its old statement stays
unchanged. `through_prefix` transports candidate facts across actual calls and
preparation. The new argument scope separately records the real table at 80,
and the call's native output contains the updated table in 76.

## Consumers

Three new kernel consumers in `Tests/SourceCacheMissSetup.lean` discharge all
three smaller recursive contracts with proved empty-input totality.

The first repeats a table-owned parent-query pointer, performs a head miss,
tail hit and left contraction hit, and derives all eleven stable prefix
boundaries, the actual exact-cost call and its native optional/table output.
The second uses arbitrary typed cached nonempty witness words of score seven
for both empty requests. The constructed matched candidate owns six Boxes,
retains total fifteen, and survives the actual left contraction call together
with complete ownership/coverage and exact original query snapshots. Cache
soundness is not assumed.

The third starts with an empty table and one externally owned nonempty word
borrowed by both original parent queries. Its head misses and inserts a key,
the tail hits, and the actual left contraction misses and inserts a different
key. Its native output table contains both inserted entries. This executes the
proved recursive empty-miss path while original external aliases and fresh
word-supported references coexist. No consumer supplies completed physical
invocation success or a desired post-callee ownership frame.

## Validation and reproduction

The 4,185-job root build and six affected Lean suites pass, including all eight
recursive runtime cases. All 1,833 unique audited endpoints, including the
thirteen new public theorems, use only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds resolve 1,304 unique declarations
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
  --out /var/tmp/subtree-left-recursion-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_call_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_call_arguments_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.AnchoredLoanMachine.advance_call \
  SubtreeProofs.Rust.SourceEval.Addressed.anchored_original_borrow_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.anchored_move_view_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.MatchedCandidateScope.through_prefix
```

All seven caches are guest-ext4 bind mounts. Cargo metadata selects the mounted
standalone-crate target and Cargo/Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-left-recursion-{build,consumer,expressions,control,helpers,
lifecycle,runtime,axioms,statements,rust,python}.log`; statement data uses the
same prefix. Source scanning supplied candidate theorem names; the kernel audit
and elaborated statement query validate the reported endpoints and assumptions.

## Remaining work

Execute the eleven remaining `contractLeft` prefix instructions 49–59: retire
moved argument roots 80/79/77; open/extract optional result 74 and table 75 from
76; drop the moved-out tuple; end root 78; retire root 76; open payload storage
81. Narrow back to the original loan family when the fresh views end, and
construct the real optional-result inspection. Complete left failure/success
joins and the right contraction path.

Derive recursive witness owner provenance or equivalent selected destructor
loan-disjointness from actual source execution for general owned cleanup.
Original-query destructor permissions remain separate from fresh-word anchor
permissions. Complete overflow exits, choice, insertion, remaining parent
return/closure and full pair/pair `NativeTotal` induction. Dynamic parsed
regions/destructors, public maximum/cold-table teardown, wrappers/input policy/
resources/G3 and every other planning target remain open. Full SRC-01/C3 and
the full goal remain active; this increment proves no production resource bound.
