# Constructed root-score arithmetic and native switch

Date: 2026-11-18. Baseline: `342a742` on `Droschinsky-algos`.
Eight new modules provide fourteen public checked theorems. All twelve actual
root-score instructions now execute after successful subtotal. Parsed entry and
all six prior prefix boundaries compose at shared sufficient bounds, retaining
native root-score success/overflow and complete ownership. Full pair/pair
induction and the remaining parent paths stay open.

## Endpoints and assumptions

`SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_root_score_scope_complete`
in [`SourcePairRootScoreEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRootScoreEntry.lean)
takes independently readable native inputs and complete input/caller/external
owner resources, a parent cache miss, smaller-head/tail `NativeTotal` contracts,
independent native head/tail success equations and successful native subtotal
`U32.checked_add heads.edges tails.edges = some subtotal`. It constructs parsed
entry and all common/miss/head/tail/subtotal/root-score prefix boundaries.
The actual root-score discriminant reads local 59, whose native snapshot is
`encodeNumberOption ((U32.checked_add subtotal 1#u32).map (fun n => n.val))`.
Both root-score success and overflow are covered; no successful root-add equation
is required. The theorem retains both owned witnesses, the actual updated table,
subtotal and complete original-loan machinery at every larger bound pair.

The statement supplies no successful physical parent run, expected post-callee
owner frame, cache soundness or global owner/loan disjointness. Smaller recursive
contracts remain explicit and await full pair/pair induction. This is a prefix
construction, not a completed parent invocation for the selected route.

`pair_root_score_scope_complete` in
[`SourcePairRootScoreScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRootScoreScope.lean)
composes the twelve instructions from an existing actual subtotal scope:

- `pair_root_subtotal_complete` copies the successful optional payload through
  temporary 55 into existing subtotal local 51, retires 55, executes the actual
  fake read and retires optional storage 52. These scalar operations retain both
  owned witnesses and the updated table; they require no owned-witness drop.
- `pair_root_score_arguments_complete` opens scalar total storage 58 and option
  result storage 59, then opens/copies the retained subtotal into argument 60.
- `pair_root_score_call_complete` reuses the checked helper construction with
  the actual operand list `[move local60, number 1]`, then retires the moved
  scalar argument. `RootScoreScope` retains head/tail witnesses 37/47, table 42,
  subtotal 51, native option 59, fresh empty total storage 58 and retired roots
  52/55/60. Exact call source cost is supplied by the existing helper bridge.

`addRoot_actions` checks the unchanged twelve-instruction prefix and its real
overflow/contraction/cleanup continuations. `number_option_payload_read`,
`number_local_read` and `root_score_arguments_source` identify the actual scalar
reads and literal argument without assuming successful physical argument scans.

`original_number_assign_complete` in
[`SourceOriginalNumberAssign.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalNumberAssign.lean)
constructs the actual scalar copy into an already opened, empty, bound root.
The original-loan invariant, independent source read and scalar width supply
permissions and typed checked storage. Untouched older root bytes and original
loan origins persist. No completed assignment/store is a premise.

The four general shape theorems in
[`SourcePrefixIdentity.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePrefixIdentity.lean)
inspect actual executable record construction. `Derived.action_shape` and
`Derived.call_shape` prove that successful instructions preserve frame/count;
only storage-live/dead can change roots. `Calling.instruction_shape` and
`Calling.Prefix.shape` compose these facts across continuation-aware preparation
and actual calls. The untouched-root condition names only executed storage
instructions. These shape facts need no typed readiness or callee postcondition.
The parsed root-score endpoint uses them to derive its count and unbound-root
requirements from the already constructed earlier prefixes. They do not assert
that arbitrary physical instructions succeed.

## Consumers and verification

Two additional kernel consumers in `Tests/SourceCacheMissSetup.lean` discharge
both recursive contracts with proved empty-input totality. The first has both
parent queries alias a nonempty word in a table-owned entry. A head miss and
tail hit produce subtotal zero, then root score `Some 1`; the proof retains all
six stable prefix boundaries, retired roots and actual successful discriminant.

The second uses distinct warm keys: head score `4294967295`, tail score zero.
The native subtotal succeeds at maximum width, and adding the root edge alone
produces `None` and the actual overflow discriminant. Its left query aliases
table-owned data; its larger right query is represented by an explicit complete
external Box owner ledger. Both query graphs and all input/external owners are
constructed. No cache-soundness or successful physical-run premise is supplied.
This distinguishes root overflow from the earlier subtotal-overflow consumer.

The 4,148-job root library build and six affected Lean suites pass, including
all eight recursive runtime cases. The audit checks 1,744 unique endpoints,
including all fourteen new public theorems, with only `propext`, `Classical.choice`
and `Quot.sound`. Eight elaborated statement seeds resolve 1,295 unique
declarations with zero unknown references. Thirteen ordered Rust tests and nine
standalone Python frontend checks pass. The broader 47-suite/native-WP evidence
at `d49f638` is inherited, not rerun. No Rust source, generated extraction,
interpreter semantics, parser, shared tooling or dependency pins change.

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
  --out /var/tmp/subtree-root-score-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_root_score_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_score_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_score_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_score_arguments_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_subtotal_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.original_number_assign_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.shape \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.call_shape
```

All seven caches are guest-ext4 bind mounts. Cargo metadata selects the mounted
standalone-crate target; Cargo/Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-root-score-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log`; statement data uses the same prefix.

## Remaining work

Construct the successful root-score branch: extract the total into 58, construct
the owned matched witness in 64 from moved head/tail words and native score,
concatenate the left query into 71, then build/retire its fresh query references
and execute the smaller contraction call. Track original bounded query loans
separately from fresh word/embedding references, preserving legal aliases.

Derive recursive witness owner freshness or equivalent selected destructor
loan-disjointness from actual source execution and use the checked `drop_fresh`
bridge for owned cleanup. Complete overflow exits, both contraction paths,
choice, insertion, remaining parent return/closure and full pair/pair
`NativeTotal` induction. Dynamic parsed regions/destructors, public maximum/
cold-table teardown, wrappers/input policy/resources/G3 and every other planning
target remain. Full SRC-01/C3 and the full goal stay open; no production resource
closure follows from this increment.
