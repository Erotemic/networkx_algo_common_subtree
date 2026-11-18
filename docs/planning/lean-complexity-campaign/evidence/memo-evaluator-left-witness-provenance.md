# Left recursive witness provenance and retained candidate/query bounds

Baseline: `2db7171` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [matched-candidate bound](memo-evaluator-head-tail-candidate-provenance.md)
now survives actual left-query concatenation, fresh views, argument moves,
left recursion and all eleven result cleanup instructions. The left witness gets
its own independently derived bound; six successful-left payload instructions
transfer it into held local 81.

## Constructed concatenation and views

`pair_left_concat_call_complete_fresh` wraps the unchanged forward constructor,
then inspects its actual helper call and three cleanup instructions. Native
shared-word arguments establish readiness. The helper allocation ledger derives
the owned word's bound at 71 relative to the original parent heap. The actual
call-preservation theorem retains the independently bounded matched candidate
at 64; actual cleanup retains both inventories.

`pair_left_concat_scope_complete_fresh` composes the preceding five argument
instructions with that call/cleanup. `entry_pair_matched_queries_complete_fresh`
retains the stronger matched endpoint and independently identifies original
query snapshots using the old head checkpoint. Parsed concatenation and fresh
word-view entry variants carry both bounds through their eight/nine stable
prefix checkpoints. The fresh word's loan anchor remains separate from the
strictly original query/table/caller loan family.

## Actual left recursion and complete result cleanup

`pair_left_scope_complete_fresh` keeps the older complete forward constructor
with its smaller contract obtained via `NativeTotalFresh.total`. Its actual
argument prefix is independently reconstructed and identified by determinism.
The resulting initialized native snapshots establish readiness for the actual
recursive call. `Derived.evaluator_checkpoint_fresh_spec` uses the explicit
stronger smaller left-request contract and actual argument scans/store to derive
the tuple witness-field bound. No desired physical post-frame is supplied.

The matched candidate 64 and owned concatenated query 71 retain their canonical
owner identities across the actual recursive call. All eleven cleanup steps
retain those bounds and transfer the optional witness from tuple 76 into 74,
while the table at 75 remains unrestricted. Native outputs, exact original/fresh
query views, complete ownership/coverage, count/frame/root/heap guarantees and
the actual result discriminant persist.

`entry_pair_left_scope_complete_fresh` composes all twelve stable parsed-entry
boundaries, the actual left recursive call and its exact complete cost, and the
full sixty-instruction matched/left prefix. It additionally returns bounds at
74, 64 and 71. All parent locals at index 82 or above remain unbound. Explicit
smaller head/tail/left `NativeTotalFresh` contracts and independent native
success/checked-score equations select this path. Both possible left optional
results are supported; this does not prove their complete join.

`pair_right_payload_complete_fresh` constructs the six real successful-left
payload instructions. Witness owners move from 74 through scratch 82 into 81;
the moved scratch is dropped and physically retired. Matched candidate 64 and
owned query 71 retain their bounds. All original query snapshots, table value,
complete resources and previous exact heap guarantees survive.

Every preceding endpoint statement and both native contract definitions are
unchanged. Maintained Rust, generated files, independent specifications, source
semantics, dependency pins and shared tooling are unchanged.

## Adversarial consumer

The new `Tests/SourceCacheMissSetup.lean` consumer starts with twenty old table
Box owners and original queries borrowing a nonempty table-owned word. Head,
tail and left calls hit nonempty Pair witnesses of score seven. Proved
empty-query fresh contracts discharge all three smaller requests. After parsed
entry, real left recursion, all eleven result cleanup steps and six actual
payload instructions, local 81 has exactly two bounded owners and candidate 64
still has exactly six bounded owners. Query 71 retains its bound; scratch 82 is
unbound. No cache-soundness premise or successful whole-parent invocation is
supplied.

## Validation and reproduction

The root library builds in 4,259 jobs. The complete affected parent consumer
suite passes. All 1,971 unique audited endpoints, including eight new public
theorems in eight new modules, retain only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds resolve 1,312 unique declarations
with zero unknown references.

The seven-suite/eight-runtime-case, thirteen Rust test and nine Python check
evidence at `2db7171` is inherited, not rerun for this proof-only extension.
The full 47-suite/native-WP evidence at `d49f638` is also inherited. All seven
build caches remain guest-ext4 bind mounts; no Rust build runs in this increment.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-left-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_payload_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_word_views_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_left_concat_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_concat_call_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_left_concat_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_matched_queries_complete_fresh
```

Machine-local evidence uses `/var/tmp/subtree-left-provenance-{concat,scope,
build,consumer,axioms,statements}.log` and the corresponding statement JSON.
Shared source scanning supplies candidate names; actual kernel audits and
elaborated statement closure establish endpoint/assumption status.

## Remaining work

Carry bounds for candidate 64, left witness 81 and word 71 through right-query
construction and the complete right recursive call. Derive and retain the right
word bound at 85, and combine these with the separately established right
witness bound at 95. Construct both actual chooseLonger calls, insertion, output
assembly and later selected owned cleanup. Complete both optional joins,
overflow/failure paths, parent returns and general pair/pair induction, including
`NativeTotalFresh`.

Dynamic regions/destructors, public maximum/cold-table teardown, wrappers/input
policy/resources/G3 and all remaining planning requirements stay open. This
increment does not close SRC-01/C3 or production resources. The full goal remains
active.
