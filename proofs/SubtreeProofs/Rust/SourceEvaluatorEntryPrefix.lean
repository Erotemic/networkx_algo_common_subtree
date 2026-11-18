module

public import SubtreeProofs.Rust.SourceEvaluatorLookupPrefix
public import SubtreeProofs.Rust.SourceOwnerEntry
public import SubtreeProofs.Rust.SourceEvaluatorEntryCertificate

/-! The actual parsed evaluator entry and constructed common lookup prefix,
from independent native inputs and complete ownership, with allowed aliases. -/

@[expose] public section


namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def inputPackets (leftCell rightCell tableCell : Cell) (left right : BalancedWord) (table : MemoTable) : List ValueCell :=
  [(leftCell, .reference (encodeWord left)), (rightCell, .reference (encodeWord right)), (tableCell, encodeTable table)]

theorem initial_inputs (left right : BalancedWord) (table : MemoTable) :
    InputLocals left right table (initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]) := by
  constructor <;> simp [initialState, Partial.Locals.lift, initialEnv, Slot.ofValue]

theorem initial_safe (left right : BalancedWord) (table : MemoTable) :
    LoanSafeState (initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table]) := by
  apply LoanSafeState.initial
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.word left)
  · simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.word right)
  · exact (NativeData.table table).loan_safe

theorem native_entry_machine {world : World} {callers : List Activation} {previous : Resources}
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
    ∃ entered active,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] ∧
      active.count = 113 ∧ (∀ slot, slot ∉ [1, 2, 3] → active.roots slot = none) := by
  dsimp only
  let packets := inputPackets leftCell rightCell tableCell left right table
  let entered := world.stackCells world.memory.length (packets.map Prod.fst)
  let active := initialActivation world world.memory.length 113 packets
  have readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
    intro p member
    simp only [packets, inputPackets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact leftRead
    · exact rightRead
    · exact tableRead
  have bound : packets.length + 1 ≤ 113 := by simp [packets, inputPackets]
  obtain ⟨entryRun, valid, wf, keep⟩ := enter_complete hw world.memory.length 113 readable bound
  have own := enter_owner_resources hw world.memory.length 113 hc readable input frame covered entryRun
  have machine : LoanSafeMachine world callers previous external entered active := by
    refine ⟨hw, view, (keep previous.reads).preserves, valid, wf, initialActivation_rootsSeparate hc _ _ _, ?_, ?_,
      initial_safe left right table, own.1, own.2⟩
    · simp only [entered, World.stackCells, List.length_append]; omega
    · intro slot binding hb
      simp only [active, initialActivation, argumentRoots] at hb
      split at hb
      next => cases hb; change world.memory.length ≤ world.memory.length + (slot - 1); omega
      next => cases hb
  refine ⟨entered, active, ?_, machine, rfl, rfl, ?_⟩
  · rw [CallingCertificate.originalEvaluator_spec.2.1]
    exact entryRun
  · intro slot member
    have one : slot ≠ 1 := by intro same; subst slot; simp at member
    have two : slot ≠ 2 := by intro same; subst slot; simp at member
    have three : slot ≠ 3 := by intro same; subst slot; simp at member
    simp only [active, initialActivation, argumentRoots, packets, inputPackets,
      List.length_cons, List.length_nil, Nat.reduceAdd]
    have no : ¬ (0 < slot ∧ slot ≤ 3) := by omega
    simp only [no, ite_false]

theorem entry_lookup_complete {world : World} {callers : List Activation} {previous : Resources}
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
      after.Valid final ∧ final.WellFormed ∧ (∀ caller ∈ callers, caller.Valid final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      LoanSafeMachine world callers previous external final after ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers afterLookup
          (borrowPrefix ++ [.call .lookup lookupArgs 4]) entered active final after := by
  dsimp only
  obtain ⟨entered, active, entryRun, machine, state, count, unbound⟩ :=
    native_entry_machine hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  obtain ⟨minFuel, minBudget, final, after, result⟩ := lookup_prefix_complete machine (by rw [count]; decide +kernel)
    left right table (state ▸ initial_inputs left right table) (by
      intro slot member
      apply unbound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  exact ⟨entered, active, minFuel, minBudget, final, after, entryRun, result⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
