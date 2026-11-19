# Parsed return storage through complete output assembly

Baseline: `9923c7d` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [output assembly checkpoint](memo-evaluator-parent-output.md) required actual
empty bound return storage at the successful-right boundary. This follow-up
derives that invariant from parsed entry and the existing actual prefixes.
The augmented right-entry endpoint exports the empty root bytes and checked local
typing alongside all preceding ownership/provenance/native guarantees. Its
composition with the unchanged finish constructor reaches `finishCode 56` without
an input premise about return storage at the later boundary.

## Typed finite prefixes

`SourceTypedPrefixes.lean` proves `Types.CodeConstraints.prefix` and
`Types.CodeConstraints.branches`. They extract finite action constraints and
branch constraints from the existing parsed source certificate.

`Calling.instruction_other_root` retains any actual non-destination local root's
raw cell across an instruction. Storage-live appends storage; storage-dead/drop
retire without changing bytes; assignment writes a distinct checked root; and a
call consumes the existing `Derived.call_preserves_other_root` contract. This
tracks actual root bytes separately from the local mask, which can be empty.

`Calling.Prefix.typed_spec` propagates validity, caller validity, well-formedness
and local typing through a successful actual prefix. Independent source action
constraints and current local typing derive each call's `TypedReady` condition.
`Calling.Prefix.typed_other_root` combines that progression with instruction root
preservation. It takes no expected final frame or final root-cell premise.
These are conditional preservation lemmas; actual prefix construction remains
provided by the existing native entry and recursive constructors.

## Actual certificate and empty-storage invariant

`SourceEvaluatorPrefixConstraints.lean` proves `evaluator_prefix_constraints`.
The existing `originalEvaluator.constraints` and checked source identity supply
all nine actual action families: common, miss, heads, tails, subtotal, root score,
matched/left contraction, right contraction and finish. Static branch projection
and actual action-list identities derive the constraints. No duplicate local
type layout, parser or source checker is introduced, and all normal branches
remain present in the original certificate.

`SourceEmptyRootStorage.lean` defines `EmptyRootStorage`: an empty logical mask
plus a bound physical root containing its actual empty tuple cell.
`EmptyRootStorage.through_prefix` retains it across typed untouched prefixes.
`Calling.Prefix.opens_empty_storage` constructs it from an actual leading
storage-live and checked remaining prefix; the allocated binding and raw cell
come from the real executor.

`SourceTypedRootStorage.lean` bundles those facts with a typed valid checkpoint.
`TypedRootStorage.through_prefix` and `Calling.Prefix.opens_typed_storage` carry
the bundle through actual execution. The existing owner/caller models, native
evaluator contracts and source semantics are unchanged.

## Parsed right-result endpoint

`SourcePairReturnStorage.lean` proves `pair_right_return_storage`. Starting with
typed parsed-entry state and eight already constructed real prefixes, it derives
return storage at the actual right-result boundary. The common prefix's first
instruction is the real `storageLive 0`; all later common instructions leave it
untouched. Miss setup, head recursion, tail recursion, subtotal, root score,
matched/left contraction and right contraction each carry its actual bytes,
empty mask and local typing forward. Calls receive their readiness from the
source certificate instead of an additional physical postcondition.

`SourcePairRightStorageEntry.lean` proves
`entry_pair_right_scope_storage_complete_provenance`. It invokes the preceding
parsed native right-entry constructor, identifies its actual initial activation
with native entry, derives initial typing from the declaration boundary and
native argument types, and applies `pair_right_return_storage` to its real
shared-bound prefixes. The new endpoint exports `EmptyRootStorage` at 0 and
`LocalsTyped originalEvaluator.locals` at the right-result checkpoint.

Every earlier hypothesis, checkpoint, native equation, complete resource bound,
root/count guarantee, witness/owned-query provenance and stable sufficient
fuel/budget bound remains exposed. The original endpoint statements and the
`NativeTotalFresh` induction contract are unchanged. No empty return-storage
premise at the later boundary, successful whole-parent run, expected post-frame,
cache soundness or universal stronger recursive instance is supplied. Generated
files, maintained Rust, source semantics and dependency pins are unchanged.

## Consumer and validation

The added consumer in `Tests/SourceCacheMissSetup.lean` uses the original parsed
fixture with twenty old table owners and queries aliasing table-owned data.
All four smaller fresh contracts are proved empty-query instances with nonempty
warm-cache witnesses. It consumes the new derived return storage, constructs
successful-right payload, both choices, insertion, output assembly and the first
eight cleanup instructions through the actual full fifty-six-instruction prefix.
The actual return tuple inventory contains thirty-eight owners: the independently
bounded six-owner witness field and thirty-two-owner inserted table. The old
table owners are unrestricted. Both owned query bounds and all five physically
retired assembly/source roots are checked. The consumer supplies no empty-root
premise at the right-result boundary.

The 4,291-job library build and all six affected Lean suites pass: parsed-parent
consumers including the new full56 path, the independent aliasing output fixture,
all parent choice orders/ties, addressed control, owner lifecycle and all eight
recursive runtime cases. All 2,020 unique audited endpoints, including twelve
new public theorems across six modules, retain only `propext`, `Classical.choice`
and `Quot.sound`. Eight elaborated statement seeds resolve 1,329 unique
declarations with no unknown references. Thirteen ordered Rust tests and nine
Python frontend checks freshly pass. All seven caches were checked as ext4 bind
mounts; Cargo metadata selects the mounted standalone target and Cargo/Rustup
homes are on ext4.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-return-storage-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_scope_storage_complete_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_return_storage \
  SubtreeProofs.Rust.SourceEval.Evaluator.evaluator_prefix_constraints \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.typed_other_root \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.typed_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.opens_typed_storage \
  SubtreeProofs.Rust.SourceEval.Addressed.EmptyRootStorage.through_prefix \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.opens_empty_storage
```

Machine-local logs use `/var/tmp/subtree-return-storage-{typed,constraints,
empty,context,entry,build,consumer,output,branches,control,lifecycle,runtime,
axioms,statements,rust,python}.log` plus source/statement JSON. Shared source
scanning supplies candidates; kernel acceptance and elaborated statement/axiom
closure establish endpoints and assumptions. Full 47-suite/native-WP evidence
at `d49f638` remains inherited, not a fresh full-suite run.

## Remaining work

Retain the older live-root/hole/empty-mask facts needed by cleanup from index 56.
The new typed prefix machinery provides validity/typing and root-byte preservation;
exact root presence and moved/payload-hole masks still need source-level facts.
Construct remaining moved witness/table/option retirement, the two owned query
drops, scalar/earlier result-hole cleanup, original query tuple and argument
retirement, then checked return and call closure.

Complete both optional joins, overflow/failure exits, remaining parent returns
and general pair/pair induction, including universal `NativeTotalFresh`.
Dynamic regions/destructors, public maximum/cold-table teardown, wrappers/input
policy/resources/G3 and every other planning requirement remain open. No
SRC-01/C3 or production resource closure is claimed. The full goal stays active.
