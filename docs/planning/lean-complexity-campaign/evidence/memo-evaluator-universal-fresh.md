# Universal checked evaluator totality and witness provenance

Baseline: `c2b4349` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [right-failure checkpoint](memo-evaluator-right-failure.md) completes the
pair/pair branch constructors. This follow-up discharges all smaller calling
contracts by well-founded induction and exports direct universal evaluator
endpoints. Every finite native word pair and arbitrary typed warm table has a
constructed checked addressed execution in the existing source interpretation,
with complete ownership, protected caller reads, fresh witness owners and exact
larger-bound stability. Dynamic parsed-region/destructor interpretation, public
maximum and the remaining campaign scope stay open.

## Branch closure and independent measure

`SourcePairNativeFreshClosure.lean` proves `pair_native_total_fresh` from the
four smaller fresh contracts. The independent functional `evaluate_total`
supplies child native equations for branch selection. The top cache hit uses the
checked fresh copy/lookup constructor. A miss splits head/tail option results,
subtotal/root checked-add results, and both contraction option results. Each arm
uses its existing complete checked source-path theorem, including every None
updated table and exact cost. No addressed parent execution, desired post-frame,
successful close or preselected fuel/budget is a premise.

`SourceEvaluatorNativeFreshTotality.lean` proves `native_total_fresh` for all
`BalancedWord` pairs. Empty-side bases reuse `native_empty_total_fresh`;
pair/pair uses the branch closure above. The four recursive requests strictly
decrease the independent sum of Dyck-word semilengths, including both native
concatenations. Existing `toDyck_appendWord` and semilength equations establish
every decrease. The input table and native frames remain universally quantified
inside the calling contract, so growing warm tables and different recursive
worlds require no cache-soundness or fixed-frame induction premise.
`native_total` projects the original weaker contract. Its definition and every
earlier branch statement remain unchanged. The old one-edge-pair theorem now
reuses the universal instance with its original statement unchanged.

## Direct universal endpoints

`native_evaluate_total_fresh` in `SourceUniversalEvaluatorTotality.lean`
exposes the contract without any smaller-call hypothesis. Inputs are a
well-formed world, valid/represented caller frames, readable encoded queries
and table, actual input-owner footprint, complete output/caller/external Box
frame/coverage and guards drawn from caller reads. It constructs finite joint
thresholds, final world/packet, native option/table and full cost. It proves:

- The actual `Recursive.original` evaluator dispatch succeeds, with the same
  world, packet and complete cost at every larger sufficient fuel/budget pair.
- `Evaluation` records the pure pinned-source run at that exact cost and its
  actual generated native equation, including None and its actual updated table.
- Output is readable, final memory is well formed and protected caller reads
  retain bytes/liveness.
- Complete output/caller/external ownership and live-Box coverage hold.
- Every returned witness owner lies beyond the original heap. Table owners may
  be older; no freshness condition is imposed on the entire returned packet.

The source-evaluation field comes from the actual checked run's existing typed
refinement theorem, with native result/table equality aligning the independently
returned values. Reference inputs retain their actual shared types; no blanket
closed-local or no-alias assumption is introduced.

`native_evaluate_total_consistent` separately combines the universal execution
with the independent `memoized_common_embedding_refines` theorem. It preserves
that theorem's exact additional premises: `TableSound table` and both input
semilengths below 2^32. It returns Some, the independently specified mathematical
witness (`Consistent`), a sound updated table, and every source/cost/resource/
provenance/stability guarantee above. Universal execution itself needs neither
cache soundness nor those size bounds and retains all native overflow behavior.
Correctness of the mathematical result does not establish production complexity.

## Concrete consumers

`Tests/SourceUniversalFresh.lean` uses two references to the same old seven-owner
three-edge query and an empty table. No smaller calling contract, native result,
physical success or expected post-frame is supplied. The kernel consumer applies
the direct consistent endpoint with checked cold-cache soundness and width
bounds. It constructs a mathematical witness/sound output table, pure source and
actual checked dispatch at the same full cost, complete output/external ownership
and coverage, witness provenance and both forms of larger-bound stability.
All old query owners remain covered. This larger pair/pair consumer needs the
general induction rather than the previous one-edge instance.

`Tests/SourceRecursiveExecution.lean` adds `universal-cold-three-edge`. Its pure
source execution takes 56,435 steps and 37 solver calls. The case executes checked
dispatch with fuel 64/readback budget 128, compares the complete value/table/cost,
checks suspended caller guard bytes/liveness and validates owner uniqueness,
live-Box classification, full output/caller coverage and retirement of every
other new storage cell. The helper accepts an explicit optional fuel while its
existing cases retain their default 48. The runtime suite has fourteen cases;
its larger checked run is still being validated below.

## Validation

The 4,343-job library build and eleven affected Lean suites pass. The fourteen-
case runtime suite, including the larger checked run, is still running in its
original process. All 2,121 unique audited endpoints, including five new theorems
in three new proof modules, retain only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds export 1,084 unique records with
zero unknown references. Source scans identify candidates; accepted status
comes from Lean and the axiom audit. Thirteen ordered Rust tests and nine Python
frontend checks freshly pass. The new kernel consumer is included in ordinary
verification CI. CI lists fifty-six suites; this checkpoint runs the twelve
affected suites, not all fifty-six. Full 47-suite/native-WP evidence at `d49f638`
remains inherited.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceUniversalFresh.lean)
(cd proofs && lake env lean Tests/SourceRightFailure.lean)
(cd proofs && lake env lean Tests/SourceLeftFailure.lean)
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
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-universal-fresh-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-universal-fresh-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_evaluate_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_evaluate_total_consistent \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_total \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_native_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.NativeTotalFresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.NativeTotalFresh.total \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_minimal_pair_total_fresh
```

Logs use `/var/tmp/subtree-universal-fresh-{totality,direct,build,consumer,parent,
right,left,root,subtotal,none,output,choices,control,lifecycle,runtime,axioms,
statements,rust,python}.log`, plus source/statement JSON. The accepted direct and
library builds include the universal closure/induction/projection proofs; earlier
failed drafts are superseded by those accepted builds. The runtime imports the
unchanged owner/recursive source implementation and runs in one retained
process; its session/process/log metadata is in
`/var/tmp/subtree-universal-fresh-runtime-state.json` on this VM. Inspect that
actual process/session before any restart; its result is explicitly pending at
this checkpoint. Other affected regression suites start after the complete
library rebuild. All seven caches are checked ext4 bind mounts; Cargo metadata selects
the mounted standalone target and Cargo/Rustup homes are local ext4.

## Remaining work and interpretation boundary

The universal evaluator's addressed-source existence and adequacy obligation is
now proved under the existing native frame model. Compose the public seven-local
maximum body, cold-table provenance/teardown and remaining checked cleanup/cost
traces. Integrate actual dynamic parsed-region and destructor-instance
interpretation, including escape checks and scalar/stack-root protection.
Source-operation interpretation is the explicit D12 scope; Charon/Aeneas import,
primitive/runtime/provenance, mutable/unwind, compiler and physical allocator
boundaries remain explicit. Logical retirement is not physical allocator time,
peak space or a whole Rust compiler/machine theorem.
Indexed/token/reconstruction wrappers, input/error policy, G3 adversaries,
W04/MEM-03/W05/MEM-04 resources, representations/global time/space, APP and all
other mathematical/software/release/application planning requirements remain.
No full SRC-01/C3 or production resource closure is claimed; the full goal stays
active. IEEE-754 correctness remains excluded from the initial scope.
