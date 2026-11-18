module

public import SubtreeProofs.Rust.SourceNativeQueryView

/-! Construct the ten actual storage/reference instructions before evaluator
lookup. The continuation used by every reference preparation is the pinned
body's real continuation. Table/query views may share arbitrary native graphs. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem borrow_prefix_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    (count : 9 ≤ active.count) (left right : BalancedWord) (table : MemoTable)
    (inputs : InputLocals left right table active.state)
    (unbound : ∀ slot ∈ [0, 4, 5, 6, 7, 8], active.roots slot = none) :
    ∃ (final : World) (after : Activation) (resultRoot tableView leftView rightView : Binding),
      Calling.Prefix callee callers lookupSuffix borrowPrefix world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      after.count = active.count ∧ after.roots 4 = some resultRoot ∧ after.roots 5 = some tableView ∧
      after.roots 7 = some leftView ∧ after.roots 8 = some rightView ∧
      final.memory[resultRoot.address]? = some (.node .tuple 0 []) ∧ after.state 4 = .empty ∧
      after.state 5 = .shared (encodeTable table) ∧ after.state 7 = .shared (encodeWord left) ∧
      after.state 8 = .shared (encodeWord right) := by
  obtain ⟨openedWorld, opened, returnRoot, resultRoot, firstView, secondView, storage, openedMachine, openedInputs,
    openedCount, returnBinding, resultBinding, firstBinding, secondBinding, resultMemory, firstMemory, secondMemory,
    resultEmpty, firstEmpty, secondEmpty, seven, eight⟩ := storage_prefix_complete h callee count left right table inputs unbound
  obtain ⟨tableWorld, tables, tableSteps, tableMachine, tableInputs, tableRoots, tableCount, tableEmpty, tableValue, tableMemory⟩ :=
    table_views_complete openedMachine callee left right table openedInputs resultBinding firstBinding secondBinding
      resultMemory firstMemory secondMemory resultEmpty firstEmpty secondEmpty
  have tableResult : tables.roots 4 = some resultRoot := by rw [tableRoots]; exact resultBinding
  have tableFirst : tables.roots 5 = some firstView := by rw [tableRoots]; exact firstBinding
  obtain ⟨leftWorld, leftState, leftSteps, leftMachine, leftRoots, leftCount, leftValue, leftKeep, leftEmpty, leftMemory⟩ :=
    query_view_complete tableMachine callee (borrowCode 8) 7 1 left tableInputs.left
      (by rw [tableCount, openedCount]; omega) (by rw [tableRoots]; exact seven)
  have leftInputs : InputLocals left right table leftState.state := by
    refine ⟨?_, ?_, ?_⟩
    · rw [leftKeep 1 (by decide) (borrow_observes_inputs 6 (by decide) 1 (by simp))
        (borrow_observes_inputs 7 (by decide) 1 (by simp))]; exact tableInputs.left
    · rw [leftKeep 2 (by decide) (borrow_observes_inputs 6 (by decide) 2 (by simp))
        (borrow_observes_inputs 7 (by decide) 2 (by simp))]; exact tableInputs.right
    · rw [leftKeep 3 (by decide) (borrow_observes_inputs 6 (by decide) 3 (by simp))
        (borrow_observes_inputs 7 (by decide) 3 (by simp))]; exact tableInputs.table
  have leftResult : leftState.roots 4 = some resultRoot := by simpa [leftRoots, Roots.set] using tableResult
  have leftFirst : leftState.roots 5 = some firstView := by simpa [leftRoots, Roots.set] using tableFirst
  have leftResultMemory := leftMemory 4 resultRoot tableResult _ tableMemory
  have leftTable : leftState.state 5 = .shared (encodeTable table) :=
    (leftKeep 5 (by decide) (by decide +kernel) (by decide +kernel)).trans tableValue
  obtain ⟨final, after, rightSteps, finalMachine, finalRoots, finalCount, rightValue, rightKeep, rightEmpty, rightMemory⟩ :=
    query_view_complete leftMachine callee lookupSuffix 8 2 right leftInputs.right
      (by rw [leftCount, tableCount, openedCount]; omega)
      (by rw [leftRoots]; simpa only [Roots.set] using tableRoots ▸ eight)
  have finalInputs : InputLocals left right table after.state := by
    refine ⟨?_, ?_, ?_⟩
    · rw [rightKeep 1 (by decide) (borrow_observes_inputs 8 (by decide) 1 (by simp))
        (borrow_observes_inputs 9 (by decide) 1 (by simp))]; exact leftInputs.left
    · rw [rightKeep 2 (by decide) (borrow_observes_inputs 8 (by decide) 2 (by simp))
        (borrow_observes_inputs 9 (by decide) 2 (by simp))]; exact leftInputs.right
    · rw [rightKeep 3 (by decide) (borrow_observes_inputs 8 (by decide) 3 (by simp))
        (borrow_observes_inputs 9 (by decide) 3 (by simp))]; exact leftInputs.table
  have finalResult : after.roots 4 = some resultRoot := by simpa [finalRoots, Roots.set] using leftResult
  have finalFirst : after.roots 5 = some firstView := by simpa [finalRoots, Roots.set] using leftFirst
  have finalLeft : after.roots 7 = some ⟨tableWorld.memory.length, tableWorld.memory.length⟩ := by
    simp only [finalRoots, leftRoots, Roots.set]; rfl
  have finalRight : after.roots 8 = some ⟨leftWorld.memory.length, leftWorld.memory.length⟩ := by
    simp only [finalRoots, Roots.set]; rfl
  have finalMemory := rightMemory 4 resultRoot leftResult _ leftResultMemory
  have finalEmpty := rightEmpty 4 (by decide) (leftEmpty 4 (by decide) tableEmpty)
  have finalTable := (rightKeep 5 (by decide) (by decide +kernel) (by decide +kernel)).trans leftTable
  have finalWord := (rightKeep 7 (by decide) (by decide +kernel) (by decide +kernel)).trans leftValue
  have queries := leftSteps.append rightSteps
  have remaining := tableSteps.append queries
  have whole := storage.append remaining
  exact ⟨final, after, resultRoot, firstView, ⟨tableWorld.memory.length, tableWorld.memory.length⟩,
    ⟨leftWorld.memory.length, leftWorld.memory.length⟩, whole, finalMachine, finalInputs,
    finalCount.trans (leftCount.trans (tableCount.trans openedCount)), finalResult, finalFirst, finalLeft, finalRight,
    finalMemory, finalEmpty, finalTable, finalWord, rightValue⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
