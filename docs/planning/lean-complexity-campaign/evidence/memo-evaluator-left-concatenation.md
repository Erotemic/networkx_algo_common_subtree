# Constructed left-query concatenation and retained native queries

Date: 2026-11-18. Baseline: `ec80c6d` on `Droschinsky-algos`.
Ten new modules provide thirty-one public checked theorems. Parsed evaluator
entry reaches the owned left contraction query through eight actual stable
prefix boundaries. The new construction executes instructions 30–38 of the
sixty-instruction `contractLeft` prefix. Fresh references to the concatenated
word and the subsequent contraction call remain open.

## Checked endpoints and explicit premises

`SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_concat_scope_complete`
in [`SourcePairLeftConcatEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftConcatEntry.lean)
takes independently readable native inputs, complete input/caller/external owner
resources, a parent cache miss, smaller-head/tail `NativeTotal` contracts and
independent native head/tail/subtotal/root success equations. It constructs
parsed entry and all eight common/miss/head/tail/subtotal/root-score/matched/
concatenation prefix boundaries at joint sufficient helper bounds. The final
machine retains the matched candidate, updated table, total, scalar-only old
witness masks, exact original native query and child-view snapshots, owned
`encodeWord (OrderedSolver.appendWord lh lt)` in local 71, retired argument
roots 72/73 and fresh future contraction slots 74–81. Both original queries may
alias table-owned data. No successful physical parent run, cache soundness,
recursive witness freshness or global alias ban is supplied.

`pair_left_concat_scope_complete` in
[`SourcePairLeftConcatScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairLeftConcatScope.lean)
constructs all nine instructions from an existing matched scope. The first five
open result storage 71 and reborrow the original native child words from views
27/28 into 72/73. The actual `.concatenate` call moves both references into the
unchanged helper and writes the appended native word into 71. The moved argument
roots retire and the actual fake read executes. Complete original-loan machinery,
activation frame/count, unchanged old bound-root bytes, exact original query
snapshots and matched scope persist. The temporary original reference family
narrows after the masks are proved empty from checked frame validity.

`original_concatenate_complete` in
[`SourceOriginalConcatenate.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalConcatenate.lean)
constructs the actual recursive helper call from original shared native words
and bound empty destination storage. Typed helper totality and the independent
`Helpers.concatenate_source` refinement identify one stable result, exact moved
masks, native append and native structural event profile. The exposed `cost` is
the complete concatenation **call** cost, including its local dispatch charge
and mapped native helper cost. It is not the cost of all eight prefixes or a
whole parent invocation. Older bound-root bytes are preserved except for the
explicit destination write.

`left_contraction_request_smaller` and `right_contraction_request_smaller` in
[`SourceContractionRequests.lean`](../../../../proofs/SubtreeProofs/Rust/SourceContractionRequests.lean)
prove both concatenated native requests strictly decrease the sum of independent
Dyck-word semilengths. These facts support induction; they do not supply totality
for either contraction request.

## Exact snapshots across actual calls

[`SourceRawMaskPreservation.lean`](../../../../proofs/SubtreeProofs/Rust/SourceRawMaskPreservation.lean)
and [`SourcePrefixCallPreservation.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePrefixCallPreservation.lean)
prove raw local-mask preservation through actual operand evaluation, stores,
assignments, arbitrary calls, instructions and prefix preparation. The generic
prefix results cover closed locals, unshared locals and shared locals observed
by the suffix. `Prefix.deterministic` identifies the final world and activation
of two actual prefixes with identical inputs. These mask results do not assume
callee success, validity or a completed post-callee frame; an actual successful
prefix is their premise. They establish no independent physical totality.

`PairQueryScope` in
[`SourcePairQueryScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairQueryScope.lean)
records both original native query references (1/2), their tuple (13), and all
four boxed-child views (27–30). Actual prefix determinism identifies the native
head checkpoint with the existing matched construction, then mask preservation
transports all seven snapshots through tail/score/root-score/matched prefixes.
`entry_pair_matched_queries_complete` supplies this strengthened checkpoint
without adding recursive totality or physical-success premises.

## Consumers

Two additional kernel consumers in `Tests/SourceCacheMissSetup.lean` discharge
both smaller contracts using proved empty-input totality. The first repeats the
same table-owned parent query pointer and derives all eight stable prefix
boundaries, exact query snapshots, the owned empty concatenation result and
retired argument roots. The second uses a larger externally owned left query
whose two child words are both nonempty, together with a table-owned right
query. A head miss followed by a tail hit produces the matched candidate and
actual recursive concatenation of both nonempty words. The resulting appended
word owns four Boxes, while original external and table-owned queries remain
readable under complete ownership and coverage. No cache soundness or completed
physical invocation is supplied.

## Validation and reproduction

The 4,168-job root build and six affected Lean suites pass, including all eight
recursive runtime cases. All 1,788 unique audited endpoints, including the
thirty-one new public theorems, use only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds resolve 1,309 unique declarations
with zero unknown references. Thirteen ordered Rust tests and nine standalone
Python frontend checks pass. The full 47-suite/native-WP evidence at `d49f638`
is inherited, not rerun. No maintained Rust, generated extraction, parser,
interpreter semantics, shared-tooling or dependency-pin changes are included.

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
  --out /var/tmp/subtree-left-concat-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_concat_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_concat_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_concatenate_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_matched_queries_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.prefix_pair_queries_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.retained_local_same_calls \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.closed_local_same_calls \
  SubtreeProofs.Rust.SourceEval.Evaluator.left_contraction_request_smaller
```

All seven caches are guest-ext4 bind mounts. Cargo metadata selects the mounted
standalone-crate target and Cargo/Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-left-concat-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log`; statement data uses the same prefix.

## Remaining work

Construct fresh references 78/77 to owned concatenated word 71 and execute the
smaller left contraction request. Track loans from original data separately
from loans into current owned word/embedding locals; a common newer heap bound
cannot establish selected permissions for older live stack roots. Preserve legal
query/table/caller aliases and retire fresh views at the actual source points.
Derive recursive witness owner provenance or equivalent selected destructor
loan-disjointness for general owned cleanup. Complete overflow exits, both
contraction paths, choice, insertion, remaining parent return/closure and full
pair/pair `NativeTotal` induction. Dynamic parsed regions/destructors, public
maximum/cold-table teardown, wrappers/input policy/resources/G3 and every other
planning target remain open. Full SRC-01/C3 and the full goal remain active;
this increment establishes no production resource closure.
