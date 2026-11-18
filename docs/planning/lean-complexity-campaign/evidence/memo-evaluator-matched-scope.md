# Constructed owned matched witness

Date: 2026-11-18. Baseline: `9a7857b` on `Droschinsky-algos`.
Ten new modules provide thirteen public checked theorems. The first thirty
actual successful-root-score instructions construct the native matched
embedding, including both real Box allocations and all moved-out temporary
cleanup. Parsed entry and seven actual prefix boundaries compose at stable
shared bounds. Concatenation/contractions and full pair/pair induction stay open.

## Checked endpoints and explicit premises

`SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_matched_scope_complete` in
[`SourcePairMatchedEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairMatchedEntry.lean)
takes independently readable native inputs and complete input/caller/external
owner resources, a parent cache miss, smaller-head/tail `NativeTotal` contracts,
independent native head/tail success equations and successful native subtotal/
root checked-add equations. It constructs parsed entry and all common/miss/
head/tail/subtotal/root-score/matched prefix boundaries. The actual successful
root-result discriminant is retained alongside complete original-loan machinery,
native matched candidate, exact local count, retired construction slots and
unbound future concatenation/contraction slots 71–81. No successful physical
parent run, expected post-callee frame, cache soundness, recursive witness
freshness or global alias ban is supplied.

`pair_matched_scope_complete` in
[`SourcePairMatchedScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairMatchedScope.lean)
constructs all thirty instructions from an existing actual root-score scope:

- `pair_matched_total_complete` copies the successful root total through 61
  into retained total local 58 and retires temporary/optional storage 61/59.
- `pair_matched_boxes_complete` opens candidate/word storage 64/65, moves the
  head and tail words through 67/69 into actual newly allocated Boxes 66/68,
  and retires their moved-out word temporaries. The old witness masks in 37/47
  retain their original scalar scores and empty moved word fields.
- `pair_matched_word_complete` moves both Boxes into native pair word 65 and
  drops/retires moved-out Box temporaries 68/66. Their owners transfer into the
  word; these zero-owner temporary drops do not destroy the transferred trees.
- `pair_matched_embedding_complete` copies total 58 into 70 and assembles
  candidate 64 from moved word 65 and score 70. It retires 70, drops/retires
  moved-out word 65 and executes the actual fake read.

`matchedWitness heads tails total = ⟨Pair heads.word tails.word, total⟩` describes
the resulting independent native value. `MatchedScope` retains its exact encoded
snapshot, updated table in 42, total in 58 and scalar-only masks in 37/47.
`resultWordHole_boxes_zero` checks those retained partial masks own no Boxes.
All construction temporaries are retired. This does not establish permissions
to destroy the owned matched candidate later, or close the parent invocation.
`contractLeft_actions` identifies the unchanged sixty-instruction source prefix,
its actual left-result switch and failure/right-contraction/cleanup joins; the
current construction covers its first thirty instructions only.

## Reusable actual owner-transfer constructions

`original_box_new_complete` in
[`SourceOriginalBoxNew.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalBoxNew.lean)
constructs the actual helper call and checked destination store from a typed,
closed local value, original-loan machinery and fresh empty bound output storage.
Typed helper totality supplies one stable actual call; source reflection derives
the exact boxed snapshot, moved source mask and complete `boxNewCallCost`.
Existing complete-owner contracts transfer the input owners plus the new Box.
No completed helper call or post-callee owner frame is a premise.

`original_boxed_word_complete` in
[`SourceOriginalBoxedWord.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalBoxedWord.lean)
constructs the common five-instruction sequence: open Box output, project a
native embedding word into a fresh temporary, call actual `boxNew`, then retire
the moved temporary. It retains the partial typed embedding, native boxed word,
complete original-loan machine, untouched closed locals and older root bytes.
Both head and tail instances reuse this proof. `result_word_take` and
`resultWordHole_typed` identify the exact partial move and remaining closed type.

`original_aggregate_two_complete` in
[`SourceOriginalAggregate.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalAggregate.lean)
constructs a real two-move constructor store into existing empty local storage.
The native constructor type, closed value, distinct slots and original loan
permissions remain explicit. It returns exact cleared operand masks, the native
aggregate and complete owner/origin invariants. Both pair-word and embedding
assembly reuse it. Generated extraction and executor semantics are unchanged.

## Consumers and validation

Two additional kernel consumers in `Tests/SourceCacheMissSetup.lean` discharge
both smaller recursive contracts with proved empty-input totality. Both parent
queries alias the same nonempty word in a table-owned entry.

The first performs a head miss and tail hit and derives all seven stable prefix
boundaries, candidate `⟨Pair Empty Empty, 1⟩`, zero-owner old witness masks,
retired construction roots and unbound future concatenation storage. The second
uses arbitrary typed cached Empty/Empty witnesses with nonempty `Pair Empty
Empty` words and score seven. The native subtotal/root totals are fourteen/
fifteen, and the constructed candidate owns six Boxes: four transferred
word descendants and two new outer Boxes. Complete ownership/coverage persists
while the Box temporaries retire. No cache soundness or successful physical-run
premise is supplied; neither consumer claims a completed parent invocation.

The 4,158-job root build and six affected Lean suites pass, including all eight
recursive runtime cases. The audit checks 1,757 unique endpoints, including all
thirteen new public theorems, with only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds resolve 1,301 unique declarations
with zero unknown references. Thirteen ordered Rust tests and nine standalone
Python frontend checks pass. The broader 47-suite/native-WP evidence at
`d49f638` is inherited, not rerun. No Rust source, generated extraction, parser,
interpreter semantics, shared tooling or dependency pin changes are included.

Reproduction, from the repository root unless shown:

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
  --out /var/tmp/subtree-matched-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_matched_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_matched_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_matched_boxes_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_matched_word_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_matched_embedding_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_boxed_word_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_box_new_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.original_aggregate_two_complete
```

All seven caches are guest-ext4 bind mounts. Cargo metadata selects the mounted
standalone-crate target; Cargo/Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-matched-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log`; statement data uses the same prefix.

## Remaining work

Retain exact original query/tuple/Box-field snapshots through the matched
prefix, alongside the already checked original loan origins. Construct left
query concatenation into 71 from 27/28, then fresh references 78/77 and the
smaller contraction request. Track original bounded loans separately from
fresh word/embedding loans. Rebasing all stack roots to a newer common bound
would not establish the required selected-root permissions. Preserve legal
query/table/caller aliases.

Derive recursive witness owner freshness or equivalent selected destructor
loan-disjointness from actual execution for general owned cleanup. Complete
overflow exits, both contraction paths, choice, insertion, remaining parent
return/closure and full pair/pair `NativeTotal` induction. Dynamic parsed
regions/destructors, public maximum/cold-table teardown, wrappers/input policy/
resources/G3 and every other planning target remain. Full SRC-01/C3 and the full
goal stay open; no production resource closure follows from this increment.
