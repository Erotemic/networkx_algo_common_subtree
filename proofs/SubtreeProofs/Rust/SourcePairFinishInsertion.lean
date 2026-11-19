module

public import SubtreeProofs.Rust.SourcePairInsertion

/-! Successful right payload, both choices and the complete actual insertion
region reach output assembly with an independent native table/result snapshot. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure FinishInsertionScope (lh lt rh rt : BalancedWord) (heads tails left right : CommonEmbedding)
    (table : MemoTable) (total : Aeneas.Std.U32) (active : Activation) : Prop where
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  endedViews : ∀ slot ∈ [27, 28, 29, 30], active.state slot = .empty
  headHole : active.state 37 = resultWordHole heads.edges
  tailHole : active.state 47 = resultWordHole tails.edges
  totalValue : active.state 58 = .number total.val
  leftWord : active.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))
  leftHole : active.state 74 = headPayloadHole
  rightWord : active.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))
  rightHole : active.state 88 = headPayloadHole
  headTableEmpty : active.state 42 = .empty
  leftTableEmpty : active.state 75 = .empty
  selected : active.state 99 = Slot.ofValue (encodeResult (selectedWitness (matchedWitness heads tails total) left right))
  tableValue : active.state 104 = Slot.ofValue (encodeTable
    (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table))
  moved : ∀ slot ∈ [64, 81, 89, 95, 100, 101, 102, 103, 105, 106, 107, 108, 109], active.state slot = .empty
  retired : ∀ slot ∈ [65, 70, 86, 87, 90, 91, 92, 93, 94, 96, 100, 101, 102, 103, 105, 106, 107, 108, 109], active.roots slot = none

theorem pair_finish_insertion_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails left total (some right) table world active)
    (above : LocalOwnersAbove before.memory.length world active 88)
    (heldAbove : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    (count : 110 ≤ active.count) (unbound : ∀ slot ∈ [96, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109], active.roots slot = none) :
    ∃ (minimumFuel minimumBudget : Nat) (choiceWorld : World) (choiceActive : Activation) (argumentWorld : World) (argumentActive : Activation)
        (callWorld : World) (callActive : Activation) (final : World) (after : Activation) (cost : Cost),
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      FinishInsertionScope lh lt rh rt heads tails left right table total after ∧
      (∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length final after slot) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 95 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) (finishActions.take 21) world active choiceWorld choiceActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 32) ((finishActions.drop 21).take 11) choiceWorld choiceActive argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (finishCode 32)) callers
          .insert pairInsertArgs 104 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) ((finishActions.drop 33).take 6) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) ((finishActions.drop 21).take 18) choiceWorld choiceActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 39) (finishActions.take 39) world active final after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, wc, ac, mc, choiceScope, selectedFresh, wordFresh,
    countC, frameC, rootsC, memoryC, stableC⟩ := pair_finish_choices_complete h scope above heldAbove (by omega)
      (by intro slot member; exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
  obtain ⟨minFuel, minBudget, wa, aa, wi, ai, final, after, cost, machine, tableAfter, selectedAfter, empty89, retired,
    countAfter, frameAfter, rootsAfter, freshAfter, sameAfter, memoryAfter, stableAfter⟩ :=
    pair_insertion_complete mc (.Pair lh lt) (.Pair rh rt) table (selectedWitness (matchedWitness heads tails total) left right)
      choiceScope.leftQuery choiceScope.rightQuery choiceScope.tableValue choiceScope.selected
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact wordFresh 71 (by simp)
          · exact wordFresh 85 (by simp)
          · exact selectedFresh)
      (by rw [countC]; exact count)
      (by intro slot member
          have outside : slot ∉ [99, 100, 101, 102, 103] := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega
          rw [rootsC slot outside]
          exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
  have preserved : ∀ slot, slot ∉ [89, 104, 105, 106, 107, 108, 109] → ∀ ty,
      SlotTyped (ac.state slot) ty → Borrow.Closed ty → after.state slot = ac.state slot := by
    intro slot outside ty typed closed
    apply sameAfter slot outside
    intro value same
    rw [same] at typed
    cases typed
    cases closed
  have finalScope : FinishInsertionScope lh lt rh rt heads tails left right table total after := by
    refine ⟨(sameAfter 13 (by decide) (by rw [choiceScope.tuple]; intro value same; cases same)).trans choiceScope.tuple,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, selectedAfter, tableAfter, ?_, ?_⟩
    · intro slot member
      have outside : slot ∉ [89, 104, 105, 106, 107, 108, 109] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega
      exact (preserved slot outside .u32 (by rw [choiceScope.endedViews slot member]; exact .empty _) .u32).trans (choiceScope.endedViews slot member)
    · exact (preserved 37 (by decide) (.adt .embedding) (by rw [choiceScope.headHole]; exact resultWordHole_typed heads.edges) (.adt .embedding)).trans choiceScope.headHole
    · exact (preserved 47 (by decide) (.adt .embedding) (by rw [choiceScope.tailHole]; exact resultWordHole_typed tails.edges) (.adt .embedding)).trans choiceScope.tailHole
    · exact (preserved 58 (by decide) .u32 (by rw [choiceScope.totalValue]; exact .number total.hmax) .u32).trans choiceScope.totalValue
    · exact (preserved 71 (by decide) (.adt .word) (by rw [choiceScope.leftWord]; exact ofValue_typed (word_typed _)) (.adt .word)).trans choiceScope.leftWord
    · exact (preserved 74 (by decide) (.adt .optional) (by rw [choiceScope.leftHole]; exact headPayloadHole_typed) (.adt .optional)).trans choiceScope.leftHole
    · exact (preserved 85 (by decide) (.adt .word) (by rw [choiceScope.rightWord]; exact ofValue_typed (word_typed _)) (.adt .word)).trans choiceScope.rightWord
    · exact (preserved 88 (by decide) (.adt .optional) (by rw [choiceScope.rightHole]; exact headPayloadHole_typed) (.adt .optional)).trans choiceScope.rightHole
    · exact (preserved 42 (by decide) .u32 (by rw [choiceScope.headTableEmpty]; exact .empty _) .u32).trans choiceScope.headTableEmpty
    · exact (preserved 75 (by decide) .u32 (by rw [choiceScope.leftTableEmpty]; exact .empty _) .u32).trans choiceScope.leftTableEmpty
    · intro slot member
      have alternatives : slot = 89 ∨ slot ∈ [64, 81, 95, 100, 101, 102, 103] ∨ slot ∈ [105, 106, 107, 108, 109] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto
      rcases alternatives with rfl | old | fresh
      · exact empty89
      · have outside : slot ∉ [89, 104, 105, 106, 107, 108, 109] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; omega
        exact (preserved slot outside .u32 (by rw [choiceScope.moved slot old]; exact .empty _) .u32).trans (choiceScope.moved slot old)
      · exact (retired slot fresh).1
    · intro slot member
      have alternatives : slot ∈ [65, 70, 86, 87, 90, 91, 92, 93, 94, 96, 100, 101, 102, 103] ∨ slot ∈ [105, 106, 107, 108, 109] := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
      rcases alternatives with old | fresh
      · have outside : slot ∉ [104, 105, 106, 107, 108, 109] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; omega
        rw [rootsAfter slot outside]; exact choiceScope.retired slot old
      · exact (retired slot fresh).2
  refine ⟨max 1 minFuel, minBudget, wc, ac, wa, aa, wi, ai, final, after, cost, machine, finalScope, freshAfter,
    countAfter.trans countC, frameAfter.trans frameC, ?_, ?_, ?_⟩
  · intro slot outside
    have first : slot ∉ [99, 100, 101, 102, 103] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
    have second : slot ∉ [104, 105, 106, 107, 108, 109] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
    rw [rootsAfter slot second, rootsC slot first]
  · intro slot binding different root raw read
    have outside : slot ∉ [99, 100, 101, 102, 103] := by
      intro member; rw [unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)] at root; cases root
    exact memoryAfter slot binding (by rw [rootsC slot outside]; exact root) raw (memoryC slot binding different root raw read)
  · intro fuel budget hf hb
    have positive : 0 < fuel := by have bound := (Nat.le_max_left 1 minFuel).trans hf; omega
    have first := (stableC fuel budget positive).2.2.2.2.1
    obtain ⟨args, called, cleanup, insert⟩ := stableAfter fuel budget ((Nat.le_max_right _ _).trans hf) hb
    exact ⟨first, args, called, cleanup, insert, Calling.Prefix.append (suffix := finishCode 39)
      (rest := (finishActions.drop 21).take 18) first insert⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
