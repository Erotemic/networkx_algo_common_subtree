# Constructed subtotal arithmetic and actual result switch

Date: 2026-11-18. Baseline: `daf1b8a` on `Droschinsky-algos`.
Seven new modules provide eleven public checked theorems. All fifteen actual
subtotal-prefix instructions now execute after native head/tail success, under
the explicit smaller-request contracts. The actual subtotal switch, complete
ownership and exact native-width result are reached. Full pair/pair induction,
root-score addition and the remaining parent paths stay open.

## Checked endpoints

`SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_score_scope_complete` in
[`SourcePairScoreEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairScoreEntry.lean)
takes independent native readable inputs, complete input/caller/external owner
resources, a parent cache miss, smaller-head/tail `NativeTotal` contracts and
independent native equations selecting head/tail success. It constructs parsed
entry and all five common/miss/head/tail/score prefix boundaries at one pair of
shared sufficient bounds. It retains both owned witnesses, the actual updated
table, original loan origins, the native `U32.checked_add` image in local 52 and
the real physical subtotal discriminant. No successful physical parent run,
supplied post-callee frame, global alias ban or cache-soundness premise is used.

`pair_score_scope_complete` in
[`SourcePairScoreScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairScoreScope.lean)
constructs all fifteen score instructions from an actual successful tail scope.
The existing first six instructions move the tail witness into 47. The new
`pair_score_arguments_complete` opens subtotal/result storage 51/52 and copies
the independent native head/tail edge counts into 53/54. Neither scalar copy
transfers witness owners. `pair_score_call_complete` executes actual checked-add
through the recursive dispatcher, then retires both scalar argument roots.
`ScoreSumScope` retains owned witnesses in 37/47, the updated table in 42,
subtotal option in 52, initialized empty subtotal storage 51 and retired roots
53/54. Both success and overflow outcomes remain in the theorem's statement.
`number_result_scrutinee_source` identifies the corresponding actual option tag.

`original_checked_add_operands_complete` in
[`SourceOriginalCheckedAdd.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalCheckedAdd.lean)
constructs an actual checked call and result store at explicit local storage.
Its inputs are original-loan machinery, a source operand derivation with two
independent in-range numbers, inline move permissions, closed/original masks,
and a bound, empty, fresh destination root. Typed helper totality supplies
stable actual execution; source reflection identifies the exact
`encodeNumberOption (checkedAdd32 left right)` and complete call cost
`checkedAddCallCost`. No completed call or output frame is assumed. The operand
list is explicit, so the later root-add literal operand can reuse this lemma.
`original_checked_add_complete` supplies the two-moved-local instance;
`number_call_arguments` supplies its source operand derivation. Existing
`checkedAdd32_native` relates the result to pinned native `U32.checked_add`.

`original_number_copy_complete` in
[`SourceOriginalNumberView.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalNumberView.lean)
constructs fresh storage and a scalar copy from an independently specified
source field. The original-loan invariant supplies the closed source typing;
a scalar read and width bound identify the copied value. All older root bytes
and original loan families remain valid. `original_open_local_complete` in
[`SourceOriginalOpenLocal.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalOpenLocal.lean)
constructs the single actual storage-live instruction with its fresh empty root
and preserved older bytes. These are shared primitives for subsequent root-score
setup, not replacement source instructions.

## Consumers and validation

Two new kernel consumers in `Tests/SourceCacheMissSetup.lean` discharge both
smaller `NativeTotal` contracts using proved empty-input instances. Both parent
queries alias the same nonempty word inside a Box owned by the transferred table.

The first performs a head miss/insertion followed by a tail hit and derives all
five stable prefix boundaries, subtotal `Some 0`, retired argument roots and the
actual successful subtotal discriminant. The second adds a typed warm
Empty/Empty entry with score `4294967295`. Both head/tail requests hit that entry;
the constructed subtotal is `None` and its actual discriminant selects overflow.
The second fixture retains table-owned query aliases, complete ownership and
coverage, and supplies no cache soundness or successful physical run premise.
These consumers prove prefix construction; neither claims a completed parent
invocation for this path.

The 4,140-job root library build and six affected Lean suites pass, including
all eight recursive runtime cases. The audit checks 1,730 unique endpoints,
including all eleven new public theorems, with only `propext`, `Classical.choice`
and `Quot.sound`. Eight elaborated statement seeds resolve 1,314 unique
declarations with zero unknown references. Thirteen ordered Rust tests and
nine standalone Python frontend checks pass. The full 47-suite/native-WP
evidence at `d49f638` is inherited, not rerun. No Rust source, generated
extraction, parser, interpreter semantics, shared tooling or dependency pins
change in this increment.

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
  --out /var/tmp/subtree-score-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_score_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_score_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_score_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_score_arguments_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_checked_add_operands_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.original_number_copy_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.original_open_local_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.number_result_scrutinee_source
```

All seven caches are guest-ext4 bind mounts. Cargo metadata selects the mounted
standalone-crate target, and Cargo/Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-score-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log`; statement data uses the same prefix.

## Remaining work

Construct all twelve root-score instructions after successful subtotal:
copy/extract the subtotal, retire optional storage, open total-result storage,
checked-add the literal one, retire its argument and inspect the native result.
Derive selected recursive witness owner freshness or equivalent loan-disjointness
from actual source execution and use the checked `drop_fresh` bridge for owned
cleanup. Complete ownership alone does not establish this provenance.

Complete overflow exits, both contraction requests, choice, insertion, remaining
parent return/closure and full pair/pair `NativeTotal` induction. Preserve legal
original query/table/caller aliases and track fresh copied/concatenated query
loans separately. Dynamic parsed regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and every other planning target
remain. Full SRC-01/C3 and the full goal stay open; no production resource
closure follows from this increment.
