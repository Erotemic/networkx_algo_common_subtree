# Complete tail scope and owned-drop support

Date: 2026-11-18. Baseline: `242db13` on `Droschinsky-algos`.
Six new modules provide nine public checked theorems. The actual pair/pair miss
path now reaches the tail-result switch after all twenty-four tail-prefix
instructions, under explicit universal contracts for the smaller head/tail
requests. The successful-tail branch also constructs its first six instructions.
Full pair/pair induction and the remaining parent paths stay open.

## Checked endpoints and assumptions

`SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_tail_scope_complete` in
[`SourcePairTailScopeEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairTailScopeEntry.lean)
takes independent native readable inputs, complete input/caller/external owner
resources, a parent cache miss, smaller-head/tail `NativeTotal` contracts and an
independent native successful head equation. It constructs parsed entry, common
lookup, miss setup, all twenty-six head instructions and all twenty-four tail
instructions at shared sufficient bounds. Its actual tail discriminant reads
local 41; both possible native tail outcomes and their exact updated tables are
retained. There is no successful physical parent run premise, global alias ban
or supplied post-callee owner frame. Cache soundness is not required.

`pair_tail_retire_complete` constructs the actual three argument storage-dead
instructions after the tail call. `pair_tail_unpack_complete` moves the optional
result and updated table from output 43 into 41/42, drops/retires the moved-out
output tuple and opens empty payload 47. These are zero-owner retirements; the
head witness in 37 remains owned. `pair_tail_scope_complete` composes the full
prefix, retaining complete original-loan machinery, the two native parent
queries, tuple, four original Box-field views, head payload hole, held head
embedding, native tail result/table, fresh payload/return storage and precise
retired/root support. `PairTailScope` states these facts explicitly.

`score_tail_payload_complete` in
[`SourcePairScoreProgram.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairScoreProgram.lean)
constructs the first six actual `addScores` instructions when the native tail
result is successful. It moves that witness through temporary 48 into existing
payload storage 47, drops/retires the moved-out temporary and executes the
actual fake read. The head witness in 37 and updated table in 42 are retained.
`addScores_actions` identifies the pinned fifteen-instruction score prefix and
its subtotal-result switch. The scalar copies and checked-add call are not yet
constructed by this endpoint.

`OriginalLoanMachine.drop_fresh` in
[`SourceOriginalOwnedDrop.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalOwnedDrop.lean)
constructs an actual checked drop of any selected owned local from its bound
root and an explicit semantic fact: every represented owned descendant address
is at least the original pre-entry heap length. Original local loans and
preserved caller reads lie below that bound, so the selected drop permission
follows, including for nonzero Box ownership. It returns the exact retired
owner count and complete original-loan machine. `Derived.drop_preserves_other_local`
proves that an actual accepted drop preserves every untouched local inventory;
this supplies original-loan transport without a global separation assumption.

The freshness premise is **not** claimed for recursive witnesses yet. Complete
unique ownership plus native snapshots alone does not establish that a returned
witness owns fresh descendants instead of old table-owned words. The actual
recursive evaluator's result/table ownership provenance must establish that
fact (or an equivalent selected loan-disjointness result) before applying the
bridge to general head/tail cleanup. Existing `NativeTotal` is unchanged.

## Consumer and validation

The additional `Tests/SourceCacheMissSetup.lean` consumer has both parent queries
select the same nonempty word in a table-owned entry. Proved empty-input totality
discharges both smaller recursive contracts: the head request misses and inserts
its result, then the tail request hits that updated table. The proof derives
all four prefix boundaries, the complete `PairTailScope`, retired roots 43–46
and the actual successful tail discriminant. No physical run premise is supplied.

The 4,133-job root build and six affected Lean suites pass, including all eight
recursive runtime cases. The audit checks 1,719 unique endpoints, including all
nine new public theorems, using only `propext`, `Classical.choice` and `Quot.sound`.
Eight elaborated statement seeds resolve 1,302 unique declarations with zero
unknown references. Thirteen ordered Rust tests and nine standalone Python
frontend checks pass. The broader 47-suite/native-WP evidence at `d49f638` is
inherited, not rerun. No generated extraction, Rust source, interpreter, parser,
shared tooling or dependency pin changes are included.

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
  --out /var/tmp/subtree-tail-scope-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_tail_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_tail_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_tail_retire_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_tail_unpack_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.tail_result_scrutinee_source \
  SubtreeProofs.Rust.SourceEval.Evaluator.score_tail_payload_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.OriginalLoanMachine.drop_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.drop_preserves_other_local
```

All seven caches are guest-ext4 bind mounts. Cargo metadata selects the mounted
standalone-crate target; Cargo/Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-tail-scope-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log`; statement data uses the same prefix.

## Remaining work

Construct scalar score copies and checked-add calls, then root-score overflow,
both contraction requests, choice, final insertion and remaining cleanup/return.
Derive selected recursive witness owner freshness or equivalent loan-disjointness
from actual source execution. Track fresh copied/concatenated query loans
separately from original query origins, preserving permitted query/table/caller
aliases. Discharge all smaller `NativeTotal` contracts by full pair/pair induction.
Dynamic parsed regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning target remain.
Full SRC-01/C3 and the full goal stay open; no production resource closure follows.
