# Actual right recursion and complete right-result scope

Baseline: `9109a0c`, branch `Droschinsky-algos`. This increment continues
SRC-01/W06-C3 on the unchanged parsed evaluator. It constructs the remaining
21 instructions of the right-contraction region and composes the entire
36-instruction region. Full parent evaluator totality and production resource
bounds remain open.

## Checked endpoints and premises

`SourceEval.Evaluator.entry_pair_right_scope_complete` in
[`SourcePairRightScopeEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightScopeEntry.lean)
constructs execution from parsed evaluator entry through seventeen stable actual
prefix checkpoints to the right-result optional switch. It retains the full
preceding sixty-instruction matched/left prefix, the successful left inspection,
both fixed actual contraction calls and their complete call costs. It exposes
the composed full 36-instruction right prefix. Every larger common helper
fuel/budget pair reaches the same worlds, activations and call costs.

The explicit recursive premises are universal `NativeTotal` for the smaller
head, tail, left-contraction and right-contraction requests. The fourth is

```lean
NativeTotal (.Pair lh lt) (OrderedSolver.appendWord rh rt)
```

The independent native head/tail/left success and checked subtotal/root addition
equations remain explicit. The left equation selects the branch actually
constructed by the preceding endpoint. The right optional result and updated
table are derived from the actual recursive call and its native equation;
no desired right result or physical post-callee frame is supplied. The endpoint
supports either native right optional result. It assumes no physical parent
success, cache soundness, recursive witness-owner freshness or global alias ban.
The established contraction measure decreases remain independent induction
support; full pair/pair induction has not been completed.

`pair_right_from_concat_complete` in
[`SourcePairRightFromConcat.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightFromConcat.lean)
constructs the remaining 21 instructions from the checked owned right-word
checkpoint. Its actual source components are:

| Indices | Actual behavior |
| --- | --- |
| 15–21 | Open output 90, reborrow original left query through 1 into 91, open 92/93 and construct fresh right-word views 93/92 into owned word 85 |
| 22–23 | Open argument 94 and move native table 75 into it |
| 24 | Execute `.evaluate [move 91, move 92, move 94] 90` |
| 25–27 | Retire moved argument roots 94/92/91 |
| 28–35 | Open/extract native option 88 and table 89, drop moved tuple 90, retire ended view 93 and output 90, then open empty payload 95 |

`pair_right_scope_complete` in
[`SourcePairRightScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightScope.lean)
constructs the table/call/cleanup portion and real optional inspection. Its
`PairRightScope` retains the owned left witness in 81, left optional hole 74,
matched candidate 64, scalar holes/total, owned left word 71 and right word 85,
exact original queries, native option/table in 88/89 and empty bound payload
95. The old table masks 42/75 are empty. Moved/ended right temporary roots and
the prior concatenation argument roots are retired. Complete ownership and Box
coverage persist. The parsed-entry theorem proves all future parent roots at
index 96 or above are unbound. Stack-root freshness does not establish recursive
witness Box-owner provenance.

## Original and fresh loan families

`pair_right_word_views_complete` in
[`SourcePairRightWordViews.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightWordViews.lean)
constructs the seven actual setup instructions in source order. Original view
91 borrows the original left query. Fresh views 93/92 borrow the owned appended
right word 85. `AnchoredLoanMachine` preserves original pre-entry loan bounds
separately from the exact owned-word read footprint, including its Box
descendants. Selected permissions permit moving the table, opening other
locals and writing the recursive result without assuming disjointness of legal
original query/table/caller aliases.

`pair_right_call_arguments_complete`, `right_contraction_call_arguments`,
`pair_right_call_complete` and `pair_right_call_prefix_complete` construct the
owned table argument and execute the actual smaller recursive call. The call
moves 91/92/94 and writes the native optional/table output in 90. The fixed
`Derived.call` endpoint exposes its complete actual cost at every larger bound
pair; this does not give the cost of the whole parent prefix or a runtime
complexity envelope.

`pair_right_call_original_complete` in
[`SourcePairRightCallOriginal.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightCallOriginal.lean)
uses actual continuation preparation during the table-argument prefix to end
intermediate view 93. The call consumes fresh view 92 and original view 91.
Closed ended masks restore the strictly original loan family using
`AnchoredLoanMachine.to_original` and `OriginalLoanMachine.narrow` before any
physical reference-root retirement. `pair_right_arguments_retire_complete`
then retires the moved arguments, and `pair_right_unpack_complete` constructs
native output extraction, moved-tuple cleanup, ended-view retirement and
payload opening. Fresh writes preserve all older heap bytes, including retired
cells; the relevant retired cells' liveness is not claimed to persist.

## Consumers

Three additional kernel consumers in `Tests/SourceCacheMissSetup.lean`
discharge all four smaller recursive contracts with proved empty-input cases:

- Repeated table-owned original query aliases derive all seventeen checkpoints,
  both exact-cost contraction calls, the full left and right region prefixes,
  exact native right result/table and all future parent roots at index 96 or
  above unbound. The right contraction performs a native table insertion.
- A fourteen-Box arbitrary typed warm-table fixture retains the nonempty left
  witness's two owners in 81 beside the six-Box matched candidate through actual
  right recursion and cleanup. Original table-owned aliases persist, all right
  temporary roots retire, and the resulting native table includes the right
  insertion. No cache soundness premise is used.
- A cold parent repeats one externally owned nonempty query. A head miss,
  tail hit, left miss and right miss produce three inserted native table keys.
  Real cleanup reaches the right optional switch with that table in 89 and
  fresh empty bound payload 95. No physical parent success is assumed.

These fixtures select successful right results. The general theorem is
parametric in the optional right result under the fourth recursive contract.
The prior nonempty four-Box right-concatenation consumer is inherited; it still
stops before a nonempty pair/pair recursive call, whose universal totality is
not supplied by the empty-input theorem.

## Validation and reproduction

The 4,214-job root build and six affected Lean suites pass, including eight
recursive runtime cases. All 1,871 unique audited endpoints, including twelve
new public theorems across ten new proof modules, retain only `propext`,
`Classical.choice` and `Quot.sound`. Eight elaborated statement seeds resolve
1,312 unique declarations with zero unknown references. Thirteen ordered Rust
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
  --out /var/tmp/subtree-right-scope-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_from_concat_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_call_original_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_call_arguments_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_word_views_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_unpack_complete
```

All seven build caches are guest-ext4 bind mounts. Cargo metadata selects the
mounted standalone-crate target; Cargo/Rustup homes are ext4. Machine-local logs
are `/var/tmp/subtree-right-scope-{build,consumer,expressions,control,helpers,
lifecycle,runtime,axioms,statements,rust,python}.log`; statement data has the same
prefix. Shared source scanning supplies candidate names; the kernel audit and
elaborated statement query establish the reported endpoints and assumptions.

## Remaining work

Complete both left/right optional failure/success joins, including successful
right payload transfer into 95, then actual choice, insertion and remaining
parent returns. Derive recursive witness owner provenance or equivalent
selected destructor loan-disjointness from actual execution for general owned
cleanup. Original query-loan destructor obligations persist independently of
fresh word-loan support and parent stack-root freshness. Complete overflow exits
and full pair/pair `NativeTotal` induction. Dynamic parsed regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and the
remaining planning targets remain open. Full SRC-01/C3 and the full user goal remain
active; this increment proves no production resource bound.
