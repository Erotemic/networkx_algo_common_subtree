module

public import SubtreeProofs.Rust.SourceOriginalConcatenate
public import SubtreeProofs.Rust.SourceHelperOwnerProvenance
public import SubtreeProofs.Rust.SourceOriginalOwnedDrop

/-! Construct native concatenation with descendant-owner provenance derived
from the actual helper allocation ledger. Original query/table/caller aliases
remain allowed while the resulting owned word can be dropped constructively. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem original_concatenate_fresh_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (l r destination : Nat) (lr : l ≠ r) (dl : destination ≠ l) (dr : destination ≠ r)
    (outside : destination ∉ exceptions) (bounded : ∀ index ∈ exceptions, index < active.count)
    (left right : BalancedWord) (first : active.state l = .shared (encodeWord left)) (second : active.state r = .shared (encodeWord right))
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = ((active.state.set l .empty).set r .empty).set destination
        (Slot.ofValue (encodeWord (OrderedSolver.appendWord left right))) ∧
      nativeCost.events = MemoSource.concatenateEvents left right ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs l r) destination).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      LocalOwnersAbove before.memory.length final after destination ∧
      (∃ discarded, Derived.drop final after callers destination =
          some (final.retire discarded, {after with state := after.state.set destination .empty}) ∧
        discarded.length = (after.state destination).dropWork.boxes ∧
        OriginalLoanMachine before callers previous external exceptions
          (final.retire discarded) {after with state := after.state.set destination .empty}) ∧
      (∀ slot binding, slot ≠ destination → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world active callers .concatenate (concatenateArgs l r) destination = some (final, after, cost) := by
  obtain ⟨fuel, budget, final, after, cost, nativeCost, machine, rootsAfter, countAfter, frameAfter, stateAfter,
    events, costEq, memory, stable⟩ :=
    original_concatenate_complete h l r destination lr dl dr outside bounded left right first second root raw empty
  let sufficient := max fuel 1
  have actual := stable sufficient budget (Nat.le_max_left _ _) (by rfl)
  have arguments := concatenate_arguments_source l r lr left right first second
  have typed : SnapshotFieldsTyped [.reference (encodeWord left), .reference (encodeWord right)] [.shared (.adt .word), .shared (.adt .word)] :=
    .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil)
  have outputType : Types.callOutput .concatenate [.shared (.adt .word), .shared (.adt .word)] = some (.adt .word) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have fresh := (Derived.original_helper_call_fresh_output sufficient budget (by omega)
    h.native.valid h.native.callersValid h.native.wellFormed (by simp [Helpers.FreshOutputHelper])
    (Derived.call_ready_from_values (callers := callers) h.native.valid arguments typed outputType) actual).weaken h.native.memoryBound
  obtain ⟨discarded, dropRun, dropLength, dropMachine⟩ := machine.drop_fresh
    (by rw [rootsAfter]; exact root) (by intro index member; rw [countAfter]; exact bounded index member) fresh
  refine ⟨sufficient, budget, final, after, cost, nativeCost, machine, rootsAfter, countAfter, frameAfter, stateAfter,
    events, costEq, fresh, ⟨discarded, dropRun, dropLength, dropMachine⟩, memory, ?_⟩
  intro largerFuel largerBudget fuelBound budgetBound
  exact stable largerFuel largerBudget ((Nat.le_max_left _ _).trans fuelBound) budgetBound

end SubtreeProofs.Rust.SourceEval.Evaluator
