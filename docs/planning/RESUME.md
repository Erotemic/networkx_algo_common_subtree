# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment establishes
[actual evaluator source types and partial-local preservation](lean-complexity-campaign/evidence/memo-evaluator-source-typing.md).
All nine actual declaration/control profiles, nested annotations and both Option
instances are kernel checked. Independent partial-local reads, owned field moves,
expressions and actions preserve declared types, holes, siblings and Box shells.
Recursive control/callee typing and addressed safety remain next. The complete
[evaluator/native functional correspondence](lean-complexity-campaign/evidence/memo-evaluator-native-totality.md)
already covers all finite native queries/warm tables and every overflow/error
path, retaining exact returned tables and full costs. W06-C3 and the full planning
goal remain open.

## Checked endpoints and scope

Eight new modules extend the existing independent Heap.Ty/Shape model with
parameterized options, accept the two actual instances in the shared type
reader, and retain exact source definitions/counts. Static constraints use
destination types for aggregates and reject moves through shared references.
The generic Option declaration is checked separately at embedding and u32.
The old lookup region reader explicitly rejects expanded options until adapted.

Public new endpoints:

- `SourceEval.TypeReader.Certificate.original_checked`, `original_boundaries`,
  `original_declarations`: all nine actual bodies, boundary prefixes, layouts
  at both Option instances and exact typed/source definition-list alignment.
- `LookupSource.Partial.SlotTyped.{materialize,get,read,take}` and
  `FieldsSlotTyped.{get,set}`: independent partial-value shape/scalar preservation.
- `LookupSource.Partial.LocalsTyped.{clear,store,read,move}` and
  `SourceEval.Types.{operand_typed,operands_typed,expression_typed,action_typed}`:
  expanded-source primitive preservation, with an explicit typed callee contract.

`LocalsTyped` constrains declared slots; separate static source bounds exclude
other accesses. Empty slots retain types without asserting initialization.
Successful snapshot typing of local references does not establish storage
liveness or dynamic addressed loan validity. Static typing of the UB leaf does
not prove it unreachable; execution still rejects it.


The preceding functional increment provides shared-control extension, full-cost nesting-fuel
monotonicity/uniqueness, all six recursive failure paths, successful choice/
insertion composition and well-founded whole-run induction. The latter decreases
the independent query Dyck-semilen sum and combines completed child fuels with
local helper depth requirements. No cache-soundness or global runtime allowance
is assumed for totality or error policy.

The public API is `SubtreeProofs.Rust.SourceEval.Evaluator`:

- `evaluate_total`: completed actual source and translated-native runs for every
  finite native word pair/table, with the same result/table and full cost.
- `evaluate_source`: actual retained JSON reading/execution plus native agreement.
- `evaluate_refines`: every completed source run, at any fuel, agrees with native.
- `evaluate_stable`, `Evaluation.unique`: result/table/full-cost stability across
  sufficient fuels. Generic `SourceEval.run_extends`/`run_unique` cover every body.
- `evaluate_consistent`: reuses the existing independent native witness/score,
  sound-table and exact numeric-`memoLcs` refinement under its original sound-cache
  and input-width hypotheses.

`SourceEvalFailures`, `SourceEvalContractFailures`, `SourceEvalSuccess` and their
refinement modules retain exact syntax/drop/callee costs. New tests cover both
checked-add overflow exits, unchanged warm tables, thirteen destructor visits
and three calls, then recursive propagation with sixteen visits and four calls.
The `destroyed` counters are already included in `work.steps`; do not bill them
again. Fuel bounds call nesting, not execution work.

The 3,898-job build, all 30 Lean suites, native WP, nine Python tests and
706-endpoint axiom audit pass. Shared statement inspection covers 752 unique
declaration records.
The accepted axiom baseline remains `propext`, `Classical.choice`, `Quot.sound`.
Production Rust, generated artifacts, execution semantics, source-control
parsing and pins are unchanged. Earlier history remains in the linked reports.

## Next work toward the full goal

1. **Recursive typing and addressed safety.** Consume the completed new static
   certificate and partial-local primitive preservation in shared-control
   induction and nesting-fuel recursive callee discharge. Establish typed initial
   locals and explicit Box/checked-add typing. Then extend/reuse addressed typed
   reachable cells, heap simulation, owner ledgers, spatial/caller separation,
   storage initialization, typed loans and retained-world parsed regions for
   partial tuples/owned-field moves and live destruction, including destructor
   glue instance typing/semantics. Do not reprove actual
   source declarations, partial typing or functional evaluator/native agreement.
   `Legacy.Bounded` is not a substitute for these types. Preserve insertion's
   owned table and possible shared aliases into it.
2. **Caller-owned-local borrows and destruction.** The old lookup borrow profile
   restricts referents to the old heap; evaluator borrows of constructed local
   values require a stronger framed interpretation. Track live local owners,
   suspended callers, source regions/storage and loan validity through moves and
   drops. Partial moves retain tags, siblings and Box shells and never move through
   shared references. Functional source/native totality alone does not establish
   these safety traces or physical frees.
3. **Public core and separate wrappers.** Compose `maximum_common_embedding`
   (the actual seven-local source body is already parsed) with evaluator totality,
   table teardown and the remaining safety/cost traces. Then indexed/token/
   reconstruction wrappers, input/error policy and required G3 adversaries.
4. **Remaining resources and research scope.** Keep W04 size/substitution,
   MEM-03/W05 unpriced input/body/key/materialization/finalization work, MEM-04,
   representation/global time/space and APP targets explicit. Complete the other
   LV/Droschinsky mathematical/software/release/application obligations in the
   main plans. A source-operation count is not production time or allocator space.

D12 permits the explicit scoped source-operation interpretation. Do not invent a
whole LLVM/compiler/physical-machine proof as a prerequisite for the initial
source pilot. Charon/Aeneas import, primitive/runtime/provenance, mutable/unwind
and physical-allocation boundaries stay explicit. Full W06-C3 still requires the
remaining typed addressed/ownership/storage/loan/region composition above.
IEEE-754 correctness remains excluded from the initial proof scope.

## Completed foundations to reuse

Do not re-extract or reprove these chains:

- [Generic memo work envelopes](lean-complexity-campaign/evidence/memo-work-envelopes.md),
  [LV correspondence](lean-complexity-campaign/evidence/memo-lv-correspondence.md)
  and [independent edit-distance client](lean-complexity-campaign/evidence/memo-edit-distance.md).
  `Complexity.Memo.eval_spec` already supplies valid storage and actual `ops.read`
  counters; generic modules have no tree/Rust import. These are declared-currency
  results, not complete source/runtime work.
- [Scoped interpreted lookup](lean-complexity-campaign/evidence/lookup-region-erasure.md):
  checked source control/types, addressed memory, exclusive/intermediate owners,
  source storage, typed shared loans, parsed regions and retained-world erasure,
  with native success/readback and unchanged costs. Earlier detailed reports
  remain in the evidence directory.
- [Actual memo helpers](lean-complexity-campaign/evidence/memo-source-primitives.md),
  [addressed ownership](lean-complexity-campaign/evidence/memo-heap-ownership.md),
  [source typing](lean-complexity-campaign/evidence/memo-source-typing.md),
  [spatial ownership](lean-complexity-campaign/evidence/memo-spatial-ownership.md),
  [storage](lean-complexity-campaign/evidence/memo-stack-initialization.md) and
  [loan/region traces](lean-complexity-campaign/evidence/memo-loan-regions.md).
  Concatenation returns fresh output; insertion puts the original table under a
  fresh tail Box and retains its occurrence ledger/caller frame. Queries/witness
  may alias into that table. Ordinary outputs contain no shared references.
- [Partial-local foundations](lean-complexity-campaign/evidence/memo-evaluator-partial-locals.md),
  [complete source profile](lean-complexity-campaign/evidence/memo-evaluator-source-profile.md),
  [expanded helper bridge](lean-complexity-campaign/evidence/memo-evaluator-helper-bridge.md),
  [owned choice](lean-complexity-campaign/evidence/memo-owned-choice.md) and
  [complete body/base paths](lean-complexity-campaign/evidence/memo-evaluator-base-paths.md).
  `SourceEvalBody` retains all normal control, metadata and the undefined-behavior
  leaf in named segments, with kernel whole-body identity. Existing seven helper
  contracts, bounded scalars and native checked-add semantics are consumed by
  evaluator totality. Use closed simp sets; broad simplification of unknown match
  arms was much slower. The successful full path uses an explicit simp step budget.

The [G1 decision](lean-complexity-campaign/evidence/g1-backend-decision.md) selects
native `Std.WP`; optional charged arlib and Lax62 pilots remain checked competitors.
G0's remaining audit, SRC-01/C3, full application runtime and other listed gates
are not closed by the functional evaluator theorem. All four presentation decks
were rendered/reviewed; regenerate ignored media via
[presentations/README.md](../../presentations/README.md). The controlled application
study and publication claim remain prospective. Full requirements remain in
[README.md](README.md), [capabilities.md](capabilities.md) and the paper plans.

## Reproduce and move machines

Follow [proofs/VERIFICATION.md](../../proofs/VERIFICATION.md). All Lake commands
run from `proofs/`; edits and VM cache setup run from the repository root.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake exe cache get && lake build)
(cd proofs && lake env lean Tests/SourceEvalRecursion.lean)
(cd proofs && lake env lean Tests/SourceEvalTypes.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Full maintained suite list is in .github/workflows/verification.yml.
# Regenerate when Rust/generator/generated inputs change:
dev/regenerate_rust_lean.sh --check
```

Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Aeneas
`5a392f4b80a4d0d05abc240eb2a7fa70622a9a35` remain pinned. Extraction supports
Linux x86_64 auto-bootstrap; other hosts need the exact tools via `AENEAS_BIN_DIR`.
The `6137120` full pinned regeneration and thirteen ordered Rust tests remain the
unchanged source-provenance/behavior baseline for subsequent proof-only changes.
Never use `cargo test --lib`'s zero-test result as that Rust behavior evidence.

Guest caches must be VM-local ext4 bind mounts, including every standalone Rust
crate target and experiment Lake project. Rerun setup after reboot; do not use
symlinks or override Cargo targets onto virtiofs. The optional shared
`submodules/aiq-lean-formalization-tools` supplies generic `leanq` statement,
dependency and axiom queries; it is not an ordinary build/runtime dependency.
