module

public import SubtreeProofs.Rust.SourceEvaluatorCommonPrefix
public import SubtreeProofs.Rust.SourceEvaluatorEntryPrefix

/-! Parsed native entry and the complete actual common evaluator prefix reach
the source lookup switch with a checked native result and initialized scope. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def lookupKey : Option CommonEmbedding → Key
  | none => .variant .optional 0
  | some _ => .variant .optional 1

def lookupBranch : Option CommonEmbedding → Nat
  | none => 1
  | some _ => 0

theorem lookup_switch_native {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (left right : BalancedWord) (table : MemoTable) (scope : LookupScope initial left right table world active) :
    Derived.scrutinee world active callers (.discriminant (.local 4)) =
      some (lookupKey (LookupEvents.lookup table left right).1, active) ∧
      Control.selectIndex (lookupKey (LookupEvents.lookup table left right).1) [(.variant .optional 1, 0)] (some 1) =
        some (lookupBranch (LookupEvents.lookup table left right).1) := by
  constructor
  · have source : SourceEval.scrutinee active.state (.discriminant (.local 4)) =
        some (lookupKey (LookupEvents.lookup table left right).1, active.state) := by
      cases answer : (LookupEvents.lookup table left right).1 <;>
        simp [SourceEval.scrutinee, splitPlace, scope.result, answer, encodeOption, Slot.ofValue, Slot.get, lookupKey]
    simpa only using Derived.scrutinee_complete h.valid h.callersValid (.discriminant (.local 4)) source (by intros; trivial)
  · cases (LookupEvents.lookup table left right).1 <;> rfl

theorem entry_common_prefix_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external))) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ entered active minimumFuel minimumBudget final after,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      active.state = initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] ∧
      active.count = 113 ∧ (∀ slot, slot ∉ [1, 2, 3] → active.roots slot = none) ∧
      LoanSafeMachine world callers previous external final after ∧ LookupScope active left right table final after ∧
      Derived.scrutinee final after callers (.discriminant (.local 4)) =
        some (lookupKey (LookupEvents.lookup table left right).1, after) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active final after := by
  dsimp only
  obtain ⟨entered, active, entryRun, machine, state, count, unbound⟩ :=
    native_entry_machine hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have inputs : InputLocals left right table active.state := by rw [state]; exact initial_inputs left right table
  obtain ⟨minFuel, minBudget, final, after, finalMachine, scope, stable⟩ := common_prefix_complete machine
    (by rw [count]; decide +kernel) left right table inputs (by
      intro slot member
      apply unbound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  exact ⟨entered, active, minFuel, minBudget, final, after, entryRun, state, count, unbound,
    finalMachine, scope, (lookup_switch_native finalMachine left right table scope).1, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
