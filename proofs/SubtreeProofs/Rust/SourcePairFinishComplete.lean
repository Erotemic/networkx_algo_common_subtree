module

public import SubtreeProofs.Rust.SourcePairFinishReturn
public import SubtreeProofs.Rust.SourceRecursiveBudget

/-! Compose successful-right payload, choices, insertion, output assembly,
all ninety-seven finish instructions and the checked return at finite bounds. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_finish_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails left total (some right) table world active)
    (above : LocalOwnersAbove before.memory.length world active 88)
    (held : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    (storage : EmptyRootStorage world active 0)
    (older : PairOlderMasks active)
    (present : rootPresence active.roots = fun slot => pairRightLiveRoots.contains slot)
    (count : 113 ≤ active.count)
    (unbound : ∀ slot ∈ [96, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112], active.roots slot = none) :
    let value := encodeOutput (some (selectedWitness (matchedWitness heads tails total) left right))
      (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table)
    ∃ minimumFuel minimumBudget final after cell cost,
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads ∧ after.Valid final ∧
      (∀ caller ∈ callers, caller.Valid final) ∧ final.WellFormed ∧
      Readable final.memory final.live cell value ∧
      (∃ owners, Footprint final.memory cell owners ∧
        OwnerFrame final (owners ++ (after.owners final ++ (callerOwners final callers ++ external))) ∧
        BoxCoverage final (owners ++ (after.owners final ++ (callerOwners final callers ++ external)))) ∧
      ResultOwnersAbove before.memory.length final.memory cell ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.exec (Recursive.original budget fuel) callers finish world active = some (.returned final after (cell, value), cost) := by
  dsimp only
  obtain ⟨root0, bound0, raw0⟩ := storage.root
  obtain ⟨minimumFuel, minimumBudget, _, _, _, _, _, _, packedWorld, packedActive,
    packedMachine, packedScope, freshPacked, heldPacked, countPacked, _, _, _, stable⟩ :=
    pair_finish_packing_complete h scope above held bound0 raw0 storage.empty count unbound
  have first56 := (stable minimumFuel minimumBudget (by rfl) (by rfl)).2.2.2.2
  have olderPacked := older.through_finish_56 first56
  have presentPacked := pair_finish_56_root_presence present first56
  obtain ⟨final, after, cell, cost, owners, returned, empty, separate, fresh, kept, valid,
    callersValid, wellFormed, readable, footprint, frame, covered, resultFresh, _⟩ :=
    pair_finish_return_complete packedMachine (Recursive.original minimumBudget minimumFuel) packedScope
      olderPacked presentPacked (by rw [countPacked]; exact count) freshPacked heldPacked
  obtain ⟨wholeCost, whole⟩ := first56.exec returned
  have full : Calling.exec (Recursive.original minimumBudget minimumFuel) callers finish world active =
      some (.returned final after (cell, encodeOutput (some (selectedWitness (matchedWitness heads tails total) left right))
        (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table)), wholeCost) := by
    rw [finish_actions]
    simpa only [finishCode, ← List.foldr_append, List.take_append_drop] using whole
  refine ⟨minimumFuel, minimumBudget, final, after, cell, wholeCost, empty, separate, fresh, kept, valid,
    callersValid, wellFormed, readable, ⟨owners, footprint, frame, covered⟩, resultFresh, ?_⟩
  intro fuel budget fuelBound budgetBound
  exact Calling.exec_extends (fun _ _ _ _ _ _ _ _ run => Recursive.original_enlarge fuelBound budgetBound run) full

end SubtreeProofs.Rust.SourceEval.Evaluator
