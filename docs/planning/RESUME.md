# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment establishes
[recursive actual-source typing and region binding](lean-complexity-campaign/evidence/memo-evaluator-recursive-typing.md).
The complete nine-definition profile now has recursive snapshot type preservation
at every fuel, with all callee contracts discharged and typed initial locals,
Box payloads and both checked-add outcomes. Actual region-bearing signatures and
locals are retained and kernel checked against the existing code/type profile.
Addressed owners/storage/local loans/destruction remain next. W06-C3 and the full
planning goal remain open.

## Checked endpoints and scope

Six new modules reuse the preceding actual type certificate and independent
partial-local model. Generic source dispatch, switches and early returns preserve
types. `BodiesTyped` and fuel induction establish actual recursive `CallsTyped`
without a typed-callee hypothesis. Preservation constrains successful runs;
it does not make arbitrary checked bodies total. The tests retain this false
neighbor and the shared-reference payload exception for polymorphic Box.

Public new endpoints:

- `SourceEval.Types.original_run_typed`: all nine ordinary functions and both
  intrinsics, every fuel, independently typed arguments and exact existing runs.
- `original_exec_typed`, `original_result_typed`, `original_execute_typed`:
  actual callbacks, returned types and retained JSON execution.
- `output_closed`, `original_represented_output_unborrowed`: deep ordinary-output
  closure, including the option/table tuple. The latter requires an explicit
  heap representation; it does not construct addressed evaluator execution.
- `SourceEval.Evaluator.evaluate_typed`, `evaluate_total_typed`,
  `evaluate_source_typed`: actual source types plus existing native agreement
  for all finite native queries/arbitrary warm tables and every error/overflow.
- `SourceEval.Regions.Certificate.original_checked`, `original_program`,
  `original_mentions_bound`: actual scoped signatures/locals, exact call-region
  arities and all descendant region-use positions, including unwind metadata.

The shared regional type/erasure/renaming/reader/value model now supports
parameterized options. The evaluator declares two signature lifetimes for three
value inputs and 247 body regions for 113 locals. Insertion has three lifetimes
for four values; owned choice has none. These are parsed binders, not lifetime
intervals. The old heap-only borrow-route restriction is not applied to new
constructed-local borrows, and its dynamic safety theorem is not transferred.

The previous [source type/partial primitive certificate](lean-complexity-campaign/evidence/memo-evaluator-source-typing.md)
remains the foundation. `LocalsTyped` constrains declared slots; static bounds
exclude other accesses. Holes keep types without asserting initialization.
Source snapshot typing and binding do not establish addressed storage liveness,
exclusive owners, live loans or destructor-instance semantics.

The completed [functional evaluator proof](lean-complexity-campaign/evidence/memo-evaluator-native-totality.md)
retains `Evaluator.evaluate_total`, `evaluate_source`, `evaluate_refines`,
`evaluate_stable`, `Evaluation.unique` and `evaluate_consistent`. No cache
soundness or witness/score consistency is needed for totality/error policy;
independent optimality/memo results keep their original sound-cache/input-width
hypotheses. Full costs retain syntax, destruction, helper events and solver calls.
`destroyed` is already included in `work.steps`; do not bill it twice. Fuel bounds
call nesting, not execution work.

Production Rust, generated artifacts, source-control parsing/execution and pins
are unchanged. The accepted axiom baseline remains `propext`, `Classical.choice`,
`Quot.sound`.
The 3,904-job build, all 32 Lean suites, native WP, nine Python tests and
734-endpoint axiom audit pass. Shared statement inspection covers 1,046 unique
declaration records with no unknown references.
See the latest evidence report for validation and scope.

## Next work toward the full goal

1. **Addressed partial moves and safety.** Reuse the completed actual
   source/type/region certificates, generic control and recursive type discharge.
   Extend the addressed typed reachable-cell model, heap simulation, owner
   ledgers, spatial/caller separation, storage initialization, typed loans and
   source-region interpretation to partial tuples/owned-field moves and live
   destruction, including destructor-instance typing/semantics. Do not reprove
   extraction, static/recursive snapshot typing, binder scope or functional
   evaluator/native agreement. `Legacy.Bounded` is not a type system. Preserve
   insertion's owned table and possible shared aliases into it.
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
(cd proofs && lake env lean Tests/SourceEvalTypeExecution.lean)
(cd proofs && lake env lean Tests/SourceEvalRegions.lean)
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
