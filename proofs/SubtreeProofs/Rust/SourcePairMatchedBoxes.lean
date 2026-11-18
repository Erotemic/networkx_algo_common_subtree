module

public import SubtreeProofs.Rust.SourcePairMatchedTotal
public import SubtreeProofs.Rust.SourceOriginalBoxedWord

/-! Prepare matched-result/word storage and execute both actual Box allocations.
The original witnesses retain scalar-only masks; their words transfer into the
two Boxes that will form the matched candidate. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure MatchedBoxesScope (heads tails : CommonEmbedding) (table : MemoTable) (total : Aeneas.Std.U32)
    (world : World) (active : Activation) : Prop where
  headHole : active.state 37 = resultWordHole heads.edges
  tailHole : active.state 47 = resultWordHole tails.edges
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  totalValue : active.state 58 = .number total.val
  headBox : active.state 66 = Slot.ofValue (.boxed (encodeWord heads.word))
  tailBox : active.state 68 = Slot.ofValue (.boxed (encodeWord tails.word))
  headBoxRoot : ∃ binding, active.roots 66 = some binding
  tailBoxRoot : ∃ binding, active.roots 68 = some binding
  candidateEmpty : active.state 64 = .empty
  candidateRoot : ∃ binding, active.roots 64 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  wordEmpty : active.state 65 = .empty
  wordRoot : ∃ binding, active.roots 65 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  retired : ∀ slot ∈ [67, 69], active.roots slot = none

theorem pair_matched_boxes_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : MatchedTotalScope heads tails table total active) (count : 70 ≤ active.count)
    (unbound : ∀ slot ∈ [64, 65, 66, 67, 68, 69], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedBoxesScope heads tails table total final after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [64, 65, 66, 67, 68, 69] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
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
  obtain ⟨fuelH, budgetH, wh, ah, mh, countH, frameH, holeH, boxH, retiredH, rootH, rootsH, closedH, memoryH, stableH⟩ :=
    original_boxed_word_complete mp 37 66 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [count65, count64] <;> omega)
      (by rw [count65, count64]; omega) (by rw [count65, count64]; omega)
      (by simpa [roots65, roots64, Roots.set] using unbound 66 (by simp))
      (by simpa [roots65, roots64, Roots.set] using unbound 67 (by simp)) heads headsP (matchedCode 13)
  have tailsP : ap.state 47 = Slot.ofValue (encodeResult tails) :=
    (first2.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tailValue]; exact ofValue_typed (result_typed tails)) (.adt .embedding) rfl (by decide +kernel)).trans scope.tailValue
  have tailsH : ah.state 47 = Slot.ofValue (encodeResult tails) :=
    (closedH 47 (by decide) (by decide) (by decide) (.adt .embedding) (by rw [tailsP]; exact ofValue_typed (result_typed tails)) (.adt .embedding)).trans tailsP
  obtain ⟨fuelT, budgetT, final, after, machine, countT, frameT, holeT, boxT, retiredT, rootT, rootsT, closedT, memoryT, stableT⟩ :=
    original_boxed_word_complete mh 47 68 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [countH, count65, count64] <;> omega)
      (by rw [countH, count65, count64]; omega) (by rw [countH, count65, count64]; omega)
      (by rw [rootsH 68 (by decide) (by decide)]; simpa [roots65, roots64, Roots.set] using unbound 68 (by simp))
      (by rw [rootsH 69 (by decide) (by decide)]; simpa [roots65, roots64, Roots.set] using unbound 69 (by simp)) tails tailsH (matchedCode 18)
  have others : ∀ slot ∈ [42, 58, 64, 65], ∀ ty, SlotTyped (ap.state slot) ty → Borrow.Closed ty → after.state slot = ap.state slot := by
    intro slot member ty typed closed
    have differences : slot ≠ 37 ∧ slot ≠ 66 ∧ slot ≠ 67 ∧ slot ≠ 47 ∧ slot ≠ 68 ∧ slot ≠ 69 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    have old := closedH slot differences.1 differences.2.1 differences.2.2.1 ty typed closed
    exact (closedT slot differences.2.2.2.1 differences.2.2.2.2.1 differences.2.2.2.2.2 ty (by rw [old]; exact typed) closed).trans old
  let root64 : Binding := ⟨world.memory.length, world.memory.length⟩
  let root65 : Binding := ⟨w64.memory.length, w64.memory.length⟩
  have bound64a64 : a64.roots 64 = some root64 := by simp [roots64, root64, Roots.set]
  have bound64ap : ap.roots 64 = some root64 := by simpa [roots65, Roots.set] using bound64a64
  have bound64ah : ah.roots 64 = some root64 := by rw [rootsH 64 (by decide) (by decide)]; exact bound64ap
  have bound65ap : ap.roots 65 = some root65 := by simp [roots65, root65, Roots.set]
  have bound65ah : ah.roots 65 = some root65 := by rw [rootsH 65 (by decide) (by decide)]; exact bound65ap
  refine ⟨max fuelH fuelT, max budgetH budgetT, final, after, machine, ?_, countT.trans (countH.trans (count65.trans count64)),
    frameT.trans (frameH.trans (frame65.trans frame64)), ?_, ?_, ?_⟩
  · refine ⟨(closedT 37 (by decide) (by decide) (by decide) (.adt .embedding) (by rw [holeH]; exact resultWordHole_typed heads.edges) (.adt .embedding)).trans holeH,
      holeT, ?_, ?_, (closedT 66 (by decide) (by decide) (by decide) (.owned (.adt .word))
        (by rw [boxH]; exact ofValue_typed (.owned (word_typed heads.word))) (.owned (.adt .word))).trans boxH,
      boxT, ?_, rootT, ?_, ?_, (others 65 (by simp) .u32 (by rw [empty65]; exact .empty _) .u32).trans empty65, ?_, ?_⟩
    · have value : ap.state 42 = Slot.ofValue (encodeTable table) :=
        (first2.closed_local_same (index := 42) h.native.valid h.native.callersValid h.native.wellFormed
          (by rw [scope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) rfl (by decide +kernel)).trans scope.tableValue
      exact (others 42 (by simp) (.adt .table) (by rw [value]; exact ofValue_typed (table_typed table)) (.adt .table)).trans value
    · have value : ap.state 58 = .number total.val :=
        (first2.closed_local_same (index := 58) h.native.valid h.native.callersValid h.native.wellFormed
          (by rw [scope.totalValue]; exact .number total.hmax) .u32 rfl (by decide +kernel)).trans scope.totalValue
      exact (others 58 (by simp) .u32 (by rw [value]; exact .number total.hmax) .u32).trans value
    · obtain ⟨binding, bound⟩ := rootH
      exact ⟨binding, by rw [rootsT 66 (by decide) (by decide)]; exact bound⟩
    · have value : ap.state 64 = .empty :=
        (run65.closed_local_same (index := 64) m64.native.valid m64.native.callersValid m64.native.wellFormed
          (by rw [empty64]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans empty64
      exact (others 64 (by simp) .u32 (by rw [value]; exact .empty _) .u32).trans value
    · exact ⟨root64, by rw [rootsT 64 (by decide) (by decide)]; exact bound64ah,
        memoryT 64 root64 bound64ah _ (memoryH 64 root64 bound64ap _ (memory65 64 root64 bound64a64 _ raw64))⟩
    · exact ⟨root65, by rw [rootsT 65 (by decide) (by decide)]; exact bound65ah,
        memoryT 65 root65 bound65ah _ (memoryH 65 root65 bound65ap _ raw65)⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [rootsT 67 (by decide) (by decide)]; exact retiredH
      · exact retiredT
  · intro slot outside
    have different : slot ≠ 64 ∧ slot ≠ 65 ∧ slot ≠ 66 ∧ slot ≠ 67 ∧ slot ≠ 68 ∧ slot ≠ 69 := by simpa using outside
    rw [rootsT slot different.2.2.2.2.1 different.2.2.2.2.2, rootsH slot different.2.2.1 different.2.2.2.1]
    simp only [roots65, roots64, Roots.set, different.1, different.2.1, ite_false]
  · intro index binding root raw memoryRead
    have differences : index ≠ 64 ∧ index ≠ 65 ∧ index ≠ 66 ∧ index ≠ 67 := by
      constructor
      · intro same; subst index; rw [unbound 64 (by simp)] at root; cases root
      constructor
      · intro same; subst index; rw [unbound 65 (by simp)] at root; cases root
      constructor
      · intro same; subst index; rw [unbound 66 (by simp)] at root; cases root
      · intro same; subst index; rw [unbound 67 (by simp)] at root; cases root
    have root_a64 : a64.roots index = some binding := by simpa only [roots64, Roots.set, differences.1, ite_false] using root
    have root_ap : ap.roots index = some binding := by simpa only [roots65, Roots.set, differences.2.1, ite_false] using root_a64
    have root_ah : ah.roots index = some binding := by rw [rootsH index differences.2.2.1 differences.2.2.2]; exact root_ap
    exact memoryT index binding root_ah _ (memoryH index binding root_ap _ (memory65 index binding root_a64 _ (memory64 index binding root _ memoryRead)))
  · intro fuel budget fuelBound budgetBound
    have tailPrefix := stableT fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)
    have headPrefix := stableH fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
    exact Calling.Prefix.append (suffix := matchedCode 18) (rest := (matchedActions.drop 8).take 10)
      (first2.noncall_callee _ rfl) (Calling.Prefix.append (suffix := matchedCode 18)
        (rest := boxWordActions 47 68 69) headPrefix tailPrefix)

end SubtreeProofs.Rust.SourceEval.Evaluator
