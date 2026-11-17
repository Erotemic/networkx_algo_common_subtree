# Resume on another machine

Branch: `Droschinsky-algos`. The latest increment establishes
[computed frame resources and assignment](lean-complexity-campaign/evidence/memo-evaluator-derived-inventories.md).
Four modules compute finite read/owner/loan inventories from actual cells,
roots and masks, scan active/suspended activations and derive remaining store
contexts. Assignment executes the RHS once using those computed resources and
preserves source results/costs, activation validity and exact caller inventories.
Actual initial/control/callee, exclusive owner/spatial and dynamic region/
destructor traces remain next. W06-C3 and the full planning goal stay open.

## Checked endpoints and scope

Latest public endpoints, in `LookupSource.Partial.Addressed` / `.Storage`:

- `PartialGraph.resources`, `PartialGraphFields.resources`: executable tracing
  returns complete `ResourceRep` read/owner/loan lists from concrete cells/masks.
- `ResourceRep.{boxes,transport}`, `BorrowFootprint.{subset_reads,transport}`:
  exact source Box counts and retained ownership/shared-reference footprints.
- `Frame.{inspectSlot,inspect}`, `Inventory.{get,boxes,frame,context,transport}`:
  actual classified/live local inspection, finite coverage and automatically
  extracted destination-excluding contexts at the current source masks.
- `Activation.{scan_complete,scan_spec,context_complete,context_spec}`:
  finite bounded activations derive their complete represented resource lists.
- `Scanned.loan_coverage`, `scanCallers_{complete,spec}`,
  `Callers.{get,transport,loans_subset_reads}`: actual initialized loans and exact
  suspended caller inventories, preserved across changes outside their reads.
- `SourceEval.Addressed.Derived.{assign_run,assign_spec}`: compute move guards,
  execute the actual RHS once, derive the post-RHS remaining frame and store into
  the existing root. Input validity and concrete success imply source action/
  complete-cost agreement, updated activation/world validity and exact caller
  preservation, without supplied guard lists or a post-RHS context premise.

Move guards use active loans plus all caller reads. Stores protect remaining
active reads, caller reads and the RHS graph. A finite descriptor must prove its
root bound; a smaller count cannot hide live storage. The eventual control/call
interpreter must thread the complete actual caller stack. Input activation
validity is representation and boundedness, not global exclusive ownership:
owner multiplicity remains explicit and still requires `Nodup`/spatial and
Box-class proofs. Ghost scans are not additional production Rust work.

The preceding addressed operand/RHS/store foundations remain reusable:

- `PartialGraphFields.focus`, `PartialGraph.take` and `Storage.Frame.{locate,move}` preserve
  actual concrete reads, partial moved/remaining frames, aliases and Box shells.
- `SourceEval.Addressed.{operand_spec,operands_spec,expression_spec}` and
  `{operand_complete,operands_complete,expression_complete}` retain forward/
  reverse simulation for every RHS under physical `Allowed` / `AllowedExpr`.
- `Graph.{trace,guards_unique}` retains the finite concrete RHS graph.
- `Addressed.{assign_run,assign_spec,assign_complete}` is the reusable guarded
  one-pass primitive; the new derived executor now constructs its context.

The preceding write and storage-lifecycle foundation remains reusable:

Earlier endpoints, in `LookupSource.Partial.Addressed` / `.Storage`:

- `Retains.{refl,of_extends,weaken,trans,read}`, `Graph.transport`,
  `PartialGraph.{transport,owner_transport}` and field variants: preserve selected
  transitive read graphs and exact existing owner ledgers outside writes.
- `Preserves.{refl,trans,weaken}`, `Keeps.preserves`, `Loan.preserve`,
  `Frame.preserve`: compose mutable retained worlds with earlier append/retire.
- `World.{write_spec,write_preserves,writeStack_iff,writeStack_success}`,
  `World.WellFormed.write`, `Loan.write`, `Frame.write`: guarded in-place writes
  keep root identity/class/liveness/length. The raw `World.write` is not mutation
  authorization; `writeStack` checks actual stack identity/liveness/bounds/guards.
- `Frame.{erase,bind,store,endStorage}`, `World.endStack_success`: explicit
  remaining-local contexts and initialized destination/storage endpoints.
  Erasing a graph view alone does not authorize losing owners or loans.
- `SourceEval.AddressedPrimitives.{action_storageLive,action_storageDead,
  action_storageDead_nonowning,storageDead_no_owners,action_assign_store,
  action_assign_number}`: actual source markers, zero-owner teardown, store
  continuation and complete constant-number assignment at unchanged costs.

The older assignment continuation remains reusable; the new executor now
constructs the RHS result and represented intermediate frame for every RHS form.
Computed inventories now derive remaining contexts and initialized loan
coverage; actual program control/caller completeness and exclusive ownership
still need composition. Storage-dead can also end an
initialized zero-Box mask, as required by actual reference temporaries (for
example local 23 in `Evaluator.emptyLeft`); a Box shell fails this test. Active
contexts may include suspended callers' guard resources; complete traces must
supply that coverage and prove every conflict condition. Guards protect entire
roots, sufficient for these whole-local writes; arbitrary field mutation is not
covered. Parsed regional/destructor interpretation remains open.

The preceding addressable-local and reference-graph foundation remains reusable:

Earlier public endpoints, in `LookupSource.Partial.Addressed` / `.Storage`:

- `Graph.{represents,partial,mono}`, `graph_of_represents`, `Rep.graph`,
  `PartialGraph.{materialize,mono,locate,read}`: finite full/partial concrete
  reference graphs, including transitive shared targets, and actual initialized
  source projections with retained addresses.
- `World.{allocate_spec,allocate_keeps,retire_keeps}`, `World.WellFormed.{allocate,retire}`:
  classified live storage roots and retained-world transitions.
- `BoxOwners.{allocate,stack_disjoint,retire_stack}`: Box owner classification
  and separate stack storage liveness.
- `Loan.{readLive,shared,typed,keep,retire_iff}`: live full reference graphs,
  independent typed readback and exact retirement conflict criterion.
- `Frame.{empty,get,distinct,allocate,keep,weaken,retire_iff,borrow}`:
  addressable partial local frames with graph-covering live guard lists.
- `SourceEval.AddressedPrimitives.{expression_address,box_new_frame,action_drop_frame}`:
  actual source borrows/Box/drop, retained caller frames and unchanged costs.

Guards are read resources and may alias; they cover actual transitive reference
graphs and stack roots, while ownership lists still require separate complete
spatial accounting. A live outer pointer alone does not establish transitive
liveness. `Loan` is retained-data/liveness evidence; it does not certify that a
later mutation/move/mask change was legal. `Frame.keep` retains the same source
state. Initialized creation uses the actual partial mask in `Frame.borrow`.
The new `Preserves`/`Retains` transport supports in-place writes outside all
retained graph roots; the original `Keeps` append/retire APIs remain reusable. Stack
identities/generations are symbolic storage, not physical addresses or Box events.

The preceding partial owner/move/destructor foundation remains reusable:

`LookupSource.Partial.Addressed.Rep` relates existing stored cells to initialized
source masks and ordered ownership occurrences. Empty fields own nothing; node
tags, siblings and Box shells remain. `Rep.materialize` recovers old full heap
readback/footprint; `Rep.of_full` lifts existing helper/native results without
assuming all output owners are fresh or contiguous. Bounds, exact Box counts,
immutable extension and fresh Box creation reuse the existing heap model.

Earlier public endpoints:

- `Rep.take`, `Rep.take_typed`: concrete owned projection, moved full readback/
  footprint/type, remaining represented mask and ownership permutation partition.
- `Rep.destroy`, `Rep.unique`: independent addressed traversal selects exactly the
  complete owner list and original source visits/Box counts.
- `destroy_full_owned`, `destroy_packed_word`, `destroy_packed_result`: existing
  ownership intervals/native packing reuse; no copied helper implementations.
- `Rep.destroy_retire`, `retire_preserves`, `retired_not_alive`: explicit logical
  live-owner consumption and guarded-address preservation. Duplicate-free live
  owners are required; protection may contain shared aliases.
- `Separated.{of_full,take,alloc,drop,destroy_frame}`: complete owner separation
  and retained caller-owned addresses. This alone does not protect shared loans.
- `EnvRep.{of_full,store,clear,remask,move}`: concrete locals, source masks and
  per-local complete ownership lists.
- `SourceEval.AddressedPrimitives.{operand_move,box_new,action_drop,
  action_drop_retire,action_drop_cost}`: existing expanded-source primitives and
  exact complete costs, with live/guarded resource premises where needed.

Stored data remains after moves/retirement. Raw projection/readback is not an
initialization or allocation-liveness assertion. The new frame/graph contracts
now derive guards for actual initialized borrows and retained source states;
complete traces must still establish those frame premises and retirement/move
conflict conditions at every action. Logical retirement does not prove Rust glue
calls, physical allocator behavior or global space bounds.

The completed [recursive snapshot types/actual region binding](lean-complexity-campaign/evidence/memo-evaluator-recursive-typing.md)
retain `SourceEval.Types.original_run_typed`, actual JSON typing and deep ordinary
output closure, plus `SourceEval.Regions.Certificate.original_program` and all
region-use bounds for all nine bodies. The evaluator has two signature lifetimes,
247 body binders and 113 locals. These are binder IDs, not lifetime intervals.
The preceding [source/partial type certificate](lean-complexity-campaign/evidence/memo-evaluator-source-typing.md)
also remains complete; `Legacy.Bounded` is not a substitute for these types.

The completed [functional evaluator proof](lean-complexity-campaign/evidence/memo-evaluator-native-totality.md)
retains `Evaluator.evaluate_total`, `evaluate_source`, `evaluate_refines`,
`evaluate_stable`, `Evaluation.unique`, `evaluate_consistent` and the newer typed
corollaries. All finite queries/arbitrary warm tables and every overflow/error
retain exact output tables/full costs. Independent optimality/memo results keep
the original sound-cache/input-width hypotheses. `destroyed` is already included
in `work.steps`; do not bill it twice. Fuel bounds nesting, not execution work.

Production Rust, generated artifacts, existing memory/control/type/region models
and pins are unchanged. The accepted axiom baseline remains `propext`,
`Classical.choice`, `Quot.sound`.
The 3,929-job build, all 37 Lean suites, native WP, nine Python tests and
929-endpoint axiom audit pass. Shared statement inspection covers 313 unique
declarations with no unknown references.
See the latest evidence report for reproduction and scope.

## Next work toward the full goal

1. **Complete addressed control and callees.** Use the executable operand/RHS/
   assignment layer and its forward/reverse simulation. Construct actual initial
   activations from parsed local layouts, thread the complete suspended caller
   stack, and use the computed inventories/contexts through storage/drop/call/
   switch/return/control steps. Prove every physical route/check succeeds. Add
   Box/checked-add intrinsics and reuse completed
   ordinary helper heap/owner/borrow/type/source/cost chains. Preserve insertion's
   transferred table and aliases. Do not repeat extraction, snapshot/native
   evaluator totality, typing/binding, RHS simulation or graph/store primitives.
2. **Actual ownership, loans and lifetimes.** Carry complete exclusive Box owner/
   spatial resources alongside the read graphs through the 113-local evaluator.
   Compose computed active/suspended loan coverage with temporary ownership
   during operand lists and newly created references. `Frame.move` retains data
   resources but cannot authorize invalidating a loan; a supplied incomplete
   guard cannot do so either. Initialized zero-owner locals can end storage;
   owners/Box shells must move or drop first. Protect the affected stack root
   as well as owned Box roots, including scalar/zero-owner teardown. Complete
   dynamic parsed-region
   and destructor-instance typing/semantics along actual branches/calls. Keep
   physical allocator/compiler/runtime boundaries explicit under D12.
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
(cd proofs && lake env lean Tests/SourcePartialHeap.lean)
(cd proofs && lake env lean Tests/SourceLocalBorrow.lean)
(cd proofs && lake env lean Tests/SourceFrameUpdates.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceFrameInventory.lean)
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
