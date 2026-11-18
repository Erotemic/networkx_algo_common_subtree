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
      after.state 8 = .shared (encodeWord right) ∧ after.state 6 = .empty ∧
      (∃ secondView pointer, after.roots 6 = some secondView ∧ final.memory[secondView.address]? = some (.shared pointer)) ∧
      (∃ returnRoot, after.roots 0 = some returnRoot ∧ final.memory[returnRoot.address]? = some (.node .tuple 0 [])) ∧
      (∀ index, index ∉ [0, 4, 5, 6, 7, 8] → after.roots index = active.roots index) ∧ after.state 0 = .empty ∧
      (QueryOrigins world active before.memory.length → QueryOrigins final after before.memory.length) := by
  obtain ⟨openedWorld, opened, returnRoot, resultRoot, firstView, secondView, storage, openedMachine, openedInputs,
    openedCount, returnBinding, resultBinding, firstBinding, secondBinding, resultMemory, firstMemory, secondMemory,
    resultEmpty, firstEmpty, secondEmpty, seven, eight, returnMemory, openedOther, returnEmpty, openedQueries⟩ := storage_prefix_complete h callee count left right table inputs unbound
  obtain ⟨tableWorld, tables, tableSteps, tableMachine, tableInputs, tableRoots, tableCount, tableEmpty, tableValue, tableMemory, tableSix, tableSixMemory, tableOther, tableEmptyOther, tableQueries⟩ :=
    table_views_complete openedMachine callee left right table openedInputs resultBinding firstBinding secondBinding
      resultMemory firstMemory secondMemory resultEmpty firstEmpty secondEmpty
  have tableResult : tables.roots 4 = some resultRoot := by rw [tableRoots]; exact resultBinding
  have tableFirst : tables.roots 5 = some firstView := by rw [tableRoots]; exact firstBinding
  obtain ⟨leftWorld, leftState, leftSteps, leftMachine, leftRoots, leftCount, leftValue, leftKeep, leftEmpty, leftMemory, leftEnded, leftQueries, _⟩ :=
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
  obtain ⟨final, after, rightSteps, finalMachine, finalRoots, finalCount, rightValue, rightKeep, rightEmpty, rightMemory, rightEnded, rightQueries, _⟩ :=
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
  have leftSix : leftState.state 6 = .empty := leftEnded 6 (encodeTable table) (by decide)
    (by rw [tableCount, openedCount]; omega) tableSix (by decide +kernel)
  have finalSix : after.state 6 = .empty := rightEmpty 6 (by decide) leftSix
  have tableSecond : tables.roots 6 = some secondView := by rw [tableRoots]; exact secondBinding
  have leftSecond : leftState.roots 6 = some secondView := by simpa [leftRoots, Roots.set] using tableSecond
  have finalSecond : after.roots 6 = some secondView := by simpa [finalRoots, Roots.set] using leftSecond
  obtain ⟨secondPointer, secondMemory⟩ := tableSixMemory
  have leftSecondMemory := leftMemory 6 secondView tableSecond _ secondMemory
  have finalSecondMemory := rightMemory 6 secondView leftSecond _ leftSecondMemory
  have finalWord := (rightKeep 7 (by decide) (by decide +kernel) (by decide +kernel)).trans leftValue
  have queries := leftSteps.append rightSteps
  have remaining := tableSteps.append queries
  have whole := storage.append remaining
  refine ⟨final, after, resultRoot, firstView, ⟨tableWorld.memory.length, tableWorld.memory.length⟩,
    ⟨leftWorld.memory.length, leftWorld.memory.length⟩, whole, finalMachine, finalInputs,
    finalCount.trans (leftCount.trans (tableCount.trans openedCount)), finalResult, finalFirst, finalLeft, finalRight,
    finalMemory, finalEmpty, finalTable, finalWord, rightValue, finalSix, ⟨secondView, secondPointer, finalSecond, finalSecondMemory⟩, ?_, ?_, ?_, ?_⟩
  · have tableZero : tables.roots 0 = some returnRoot := by rw [tableRoots]; exact returnBinding
    have leftZero : leftState.roots 0 = some returnRoot := by simpa [leftRoots, Roots.set] using tableZero
    have finalZero : after.roots 0 = some returnRoot := by simpa [finalRoots, Roots.set] using leftZero
    exact ⟨returnRoot, finalZero, rightMemory 0 returnRoot leftZero _
      (leftMemory 0 returnRoot tableZero _ (tableOther 0 returnRoot (by decide) (by decide) returnBinding _ returnMemory))⟩
  · intro index member
    have zero : index ≠ 0 := by intro same; subst index; simp at member
    have four : index ≠ 4 := by intro same; subst index; simp at member
    have five : index ≠ 5 := by intro same; subst index; simp at member
    have six : index ≠ 6 := by intro same; subst index; simp at member
    have seven : index ≠ 7 := by intro same; subst index; simp at member
    have eight : index ≠ 8 := by intro same; subst index; simp at member
    simp only [finalRoots, leftRoots, Roots.set, eight, seven, ite_false, tableRoots]
    exact openedOther index (by simp [zero, four, five, six])
  · exact rightEmpty 0 (by decide) (leftEmpty 0 (by decide)
      (tableEmptyOther 0 (by decide) (by decide) returnEmpty))
  · intro queries
    have atTable := tableQueries (openedQueries queries)
    have atLeft := leftQueries tableInputs.references atTable (by decide)
    exact rightQueries leftInputs.references atLeft (by decide)

end SubtreeProofs.Rust.SourceEval.Evaluator
