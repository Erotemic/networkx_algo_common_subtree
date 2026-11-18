# Complete root-overflow dispatch and scalar cleanup

Baseline: `bc1fbc2` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [subtotal-overflow checkpoint](memo-evaluator-subtotal-overflow.md) constructs
the first checked-add failure. This follow-up constructs the complete root-edge
overflow return: both smaller results succeed, their subtotal fits, and adding
one root edge overflows. Both retained owned witnesses are dropped. The two
contraction-failure returns and universal pair/pair induction remain open.

## Derived root checkpoint

`SourcePairOlderMasks.lean` now exposes `pair_root_older_masks`, factoring its
existing six-prefix proof before contraction. Actual typed head/tail moves and
subtotal copying derive empty table3, head optional hole31, empty head table32,
tail optional hole41 and zero owners in scalar subtotal51. The original
`pair_right_older_masks` statement remains unchanged and carries these facts
through the two later contraction prefixes.

`SourceRootOverflowContext.lean` proves `pair_root_return_storage`.
The actual common prefix opens return storage0. Checked source typing carries
its empty logical mask and empty physical root bytes through the six common,
miss, head, tail, score and root-score prefixes. No desired post-frame or return
storage premise is supplied by parsed-entry clients.

`SourceRootOverflowProgram.lean` identifies the ten actual `rootOverflow`
actions and one `cleanupSubtotal` action. `pair_root_score_root_presence`
derives eighteen bound roots from the actual root-score prefix: the fifteen
tail roots plus51/58/59. `root_overflow_pack_complete` uses the actual
`storageDead 59` suffix of failure packing, moves updated table42 into None
output0, derives result59's scalar-only owner count and retires its real storage.
It retains seventeen roots, empty42, complete original-loan resources and count.

## Failure continuation and whole original body

`root_overflow_continuation_complete` in `SourceRootOverflowContinuation.lean`
constructs the real root-overflow selection and its total-payload cleanup join
(`storageDead 58`). Derived older masks and both witness owner bounds survive.
The earlier `subtotal_overflow_cleanup_complete` then supplies the actual tail
and head witness drops and shared input cleanup. Exact actual mask counts
justify storage retirement after positive owned drops. Parameter cleanup and
guarded return leave every mask empty. Four cleanup joins execute; no parent
execution or successful close is assumed. Old table/query aliases remain legal.

`entry_root_overflow_body_complete` in `SourceRootOverflowBody.lean` starts at
parsed readable pair/pair inputs and complete resources. Its recursive premises
are two explicit smaller `NativeTotalFresh` contracts. Independent native child
successes, subtotal success, root overflow and the initial lookup miss select
the path. The existing fresh root-entry constructor supplies both witness bounds.
Actual source constraints and successful payload reads establish all three
earlier optional switch tags. Root presence, older masks, empty return storage
and count come from real entry/prefixes. All six prefixes, all four cleanup joins,
the outer word/lookup routing and guarded return compose to the original body.
The natural-number/u32 literal bridge for root-edge1 is explicit.

`SourceRootOverflowTotality.lean` derives the native parent None equation and
proves `root_overflow_total_fresh`. Checked entry/closure constructs readable
None/table output, well-formedness, protected caller reads, complete output/
caller/external ownership and live-Box coverage, source/native agreement,
result-field provenance and exact world/packet/full-cost stability at all larger
sufficient fuel/budget pairs. The table may own older cells; the witness-only
freshness contract permits this. Both smaller fresh contracts still require
universal induction.

Earlier statements/contracts, independent specifications, source semantics,
generated files, maintained Rust and toolchain pins are unchanged. Logical
retirement is distinct from physical allocator cost and peak-space bounds.

## Concrete consumers

`Tests/SourceRootOverflow.lean` discharges both smaller contracts with proved
empty-input fresh instances. Two different warm keys return nonempty two-Box
witnesses scoring max u32 and zero. Their subtotal fits; only adding the root
edge fails. The left parent query borrows a nonempty word inside the old table;
the right parent query retains five external owners. The kernel consumer
constructs complete parent dispatch, readable None/table output, ten output
owners, complete output/external coverage, result provenance and stable larger
bounds. Ten output owners match the input table's size; no owner-address identity
is inferred from that count. Arbitrary typed warm caches need no soundness
premise for this source overflow case.

`Tests/SourceRecursiveExecution.lean` adds `root-overflow-owned-both` with the
same two cached nonempty witnesses. It checks 1,481 source steps and three solver
calls, full source/addressed value/table/cost equality, suspended caller guard
bytes/liveness, owner uniqueness/live-Box classification, complete output/caller
coverage and retirement of all other new storage. Both two-owner copied
witnesses must retire. The runtime suite now has eleven cases.

## Validation

The 4,328-job library build and all nine affected Lean suites pass, including
the parent proof-consumer suite restarted after the completed rebuild.
All 2,099 unique audited endpoints, including ten new theorems across six proof
modules (five new files), retain only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds export 1,333 unique records with
zero unknown references. Source scans identify candidates; accepted endpoint
status comes from Lean and the axiom audit. Thirteen ordered Rust tests and nine
Python frontend checks freshly pass. The new kernel consumer is included in
ordinary verification CI. CI lists fifty-three suites; this checkpoint freshly
ran the nine affected suites, not all fifty-three. Full 47-suite/native-WP evidence at
`d49f638` remains inherited.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceRootOverflow.lean)
(cd proofs && lake env lean Tests/SourceSubtotalOverflow.lean)
(cd proofs && lake env lean Tests/SourceNoneResultProvenance.lean)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo metadata --locked --no-deps --format-version 1 \
  --manifest-path rust/crates/verified_ordered_core/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-root-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-root-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.root_overflow_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_root_overflow_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.root_overflow_continuation_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.root_overflow_pack_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_score_root_presence \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_return_storage \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_root_older_masks \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_older_masks
```

Logs use `/var/tmp/subtree-root-{older-masks,program,continuation,body,totality,
build,consumer,parent,subtotal,none,output,choices,control,lifecycle,runtime,
axioms,statements,rust,python}.log`, plus source/statement JSON. Accepted body and
continuation rebuilds are retained in the totality/body logs; earlier failed
drafts are superseded by those accepted builds. The initial parent test started
too early during the library rebuild and reported a missing compiled dependency;
its terminal failure is retained in `subtree-root-parent-rebuild-race.log`.
The parent test passed after restarting against the successful rebuild.
All seven caches are checked ext4 bind mounts; Cargo metadata selects the mounted
standalone target and Cargo/Rustup homes are local ext4.

## Remaining work

Construct both contraction-failure returns, then universal pair/pair
`NativeTotalFresh` induction. Dynamic regions/destructors, public maximum/
cold-table teardown, wrappers/input policy/resources/G3 and every other planning
requirement remain open. No full SRC-01/C3 or production resource closure is
claimed; the full goal stays active.
