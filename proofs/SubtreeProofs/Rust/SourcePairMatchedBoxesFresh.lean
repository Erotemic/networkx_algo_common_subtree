module

public import SubtreeProofs.Rust.SourcePairMatchedBoxes
public import SubtreeProofs.Rust.SourceOriginalBoxedWordFresh

/-! Both bounded native witness words transfer through actual Box helpers.
The second allocation preserves the first Box's complete owner inventory. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_matched_boxes_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : MatchedTotalScope heads tails table total active) (headsAbove : LocalOwnersAbove before.memory.length world active 37)
    (tailsAbove : LocalOwnersAbove before.memory.length world active 47) (count : 70 ≤ active.count)
    (unbound : ∀ slot ∈ [64, 65, 66, 67, 68, 69], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedBoxesScope heads tails table total final after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [64, 65, 66, 67, 68, 69] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      LocalOwnersAbove before.memory.length final after 66 ∧ LocalOwnersAbove before.memory.length final after 68 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 18) ((matchedActions.drop 6).take 12) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨w64, a64, run64, m64, roots64, count64, frame64, empty64, raw64, memory64⟩ :=
    original_open_local_complete h callee (matchedCode 7) (slot := 64) (by decide) (by omega) (unbound 64 (by simp))
  obtain ⟨wp, ap, run65, mp, roots65, count65, frame65, empty65, raw65, memory65⟩ :=
    original_open_local_complete m64 callee (matchedCode 8) (slot := 65) (by decide) (by rw [count64]; omega)
      (by simpa [roots64, Roots.set] using unbound 65 (by simp))
  have first2 : Calling.Prefix callee callers (matchedCode 8) ((matchedActions.drop 6).take 2) world active wp ap :=
    Calling.Prefix.append (suffix := matchedCode 8) (rest := [.storageLive 65]) run64 run65
  have headsP : ap.state 37 = Slot.ofValue (encodeResult heads) :=
    (first2.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.headValue]; exact ofValue_typed (result_typed heads)) (.adt .embedding) rfl (by decide +kernel)).trans scope.headValue
  have headsPAbove := first2.owner_transfer (OwnerTransfer.kept rfl (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed headsAbove
  have tailsPAbove := first2.owner_transfer (OwnerTransfer.kept rfl (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed tailsAbove
  obtain ⟨fuelH, budgetH, wh, ah, mh, countH, frameH, holeH, boxH, retiredH, rootH, rootsH, closedH, memoryH, headFresh, headKept, stableH⟩ :=
    original_boxed_word_complete_fresh mp 37 66 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [count65, count64] <;> omega)
      (by rw [count65, count64]; omega) (by rw [count65, count64]; omega)
      (by simpa [roots65, roots64, Roots.set] using unbound 66 (by simp))
      (by simpa [roots65, roots64, Roots.set] using unbound 67 (by simp)) heads headsP headsPAbove (matchedCode 13)
  have tailsP : ap.state 47 = Slot.ofValue (encodeResult tails) :=
    (first2.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tailValue]; exact ofValue_typed (result_typed tails)) (.adt .embedding) rfl (by decide +kernel)).trans scope.tailValue
  have tailsH : ah.state 47 = Slot.ofValue (encodeResult tails) :=
    (closedH 47 (by decide) (by decide) (by decide) (.adt .embedding) (by rw [tailsP]; exact ofValue_typed (result_typed tails)) (.adt .embedding)).trans tailsP
  have tailsHAbove := headKept 47 (by rw [count65, count64]; omega) (by decide) (by decide) (by decide) tailsPAbove
  obtain ⟨fuelT, budgetT, final, after, machine, countT, frameT, holeT, boxT, retiredT, rootT, rootsT, closedT, memoryT, tailFresh, tailKept, stableT⟩ :=
    original_boxed_word_complete_fresh mh 47 68 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [countH, count65, count64] <;> omega)
      (by rw [countH, count65, count64]; omega) (by rw [countH, count65, count64]; omega)
      (by rw [rootsH 68 (by decide) (by decide)]; simpa [roots65, roots64, Roots.set] using unbound 68 (by simp))
      (by rw [rootsH 69 (by decide) (by decide)]; simpa [roots65, roots64, Roots.set] using unbound 69 (by simp)) tails tailsH tailsHAbove (matchedCode 18)
  have headsAfter := tailKept 66 (by rw [countH, count65, count64]; omega) (by decide) (by decide) (by decide) headFresh
  obtain ⟨fuelOld, budgetOld, wOld, aOld, mOld, scopeOld, countOld, frameOld, rootsOld, memoryOld, stableOld⟩ :=
    pair_matched_boxes_complete h scope count unbound
  let fuel := max fuelOld (max fuelH fuelT)
  let budget := max budgetOld (max budgetH budgetT)
  have built : Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 18)
      ((matchedActions.drop 6).take 12) world active final after :=
    Calling.Prefix.append (suffix := matchedCode 18) (rest := (matchedActions.drop 8).take 10)
      (first2.noncall_callee _ rfl) (Calling.Prefix.append (suffix := matchedCode 18)
        (rest := boxWordActions 47 68 69)
        (stableH _ _ ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
        (stableT _ _ ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)) ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  have same := built.unique (stableOld fuel budget (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  rw [same.1, same.2] at headsAfter tailFresh
  exact ⟨fuelOld, budgetOld, wOld, aOld, mOld, scopeOld, countOld, frameOld, rootsOld, memoryOld, headsAfter, tailFresh, stableOld⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
