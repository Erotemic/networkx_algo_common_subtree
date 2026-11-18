module

public import SubtreeProofs.Rust.SourcePairFinishChoices
public import SubtreeProofs.Rust.SourceOriginalBorrowView
public import SubtreeProofs.Rust.SourceMemoLoanOrigins

/-! Construct the nine actual insertion setup instructions. The table is moved,
original query views are reborrowed, and empty output/witness-view roots are
opened. Selected witness and owned contraction query provenance is retained. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_insert_setup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) (left right : BalancedWord) (table : MemoTable)
    (query1 : active.state 1 = .shared (encodeWord left)) (query2 : active.state 2 = .shared (encodeWord right))
    (tableValue : active.state 89 = Slot.ofValue (encodeTable table))
    (heldAbove : ∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length world active slot)
    (count : 110 ≤ active.count) (unbound : ∀ slot ∈ [104, 105, 106, 107, 108, 109], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (finishCode 30) ((finishActions.drop 21).take 9) world active final after ∧
      OriginalLoanMachine before callers previous external [107, 106, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state 89 = .empty ∧ after.state 105 = Slot.ofValue (encodeTable table) ∧
      after.state 106 = .shared (encodeWord left) ∧ after.state 107 = .shared (encodeWord right) ∧
      (∀ slot ∈ [104, 108, 109], after.state slot = .empty ∧
        ∃ binding, after.roots slot = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      (∀ slot, slot ∉ [104, 105, 106, 107, 108, 109] → after.roots slot = active.roots slot) ∧
      (∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [89, 104, 105, 106, 107, 108, 109] →
        (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w104, a104, run104, m104, roots104, count104, frame104, empty104, raw104, memory104⟩ :=
    original_open_local_complete h callee (finishCode 22) (slot := 104) (by decide) (by omega) (unbound 104 (by simp))
  have table104 : a104.state 89 = Slot.ofValue (encodeTable table) :=
    (run104.closed_local_same (index := 89) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) rfl (by decide)).trans tableValue
  obtain ⟨wt, aT, runTable, mt, rootsT, countT, frameT, empty89, table105, memoryT⟩ :=
    original_move_view_complete m104 callee (finishCode 24) (source := 89) (destination := 105) (by decide) (by decide)
      table104 (table_typed table) (.adt .table) (by rw [count104]; omega)
      (by simpa [roots104, Roots.set] using unbound 105 (by simp))
  have first3 : Calling.Prefix callee callers (finishCode 24) ((finishActions.drop 21).take 3) world active wt aT :=
    Calling.Prefix.append (suffix := finishCode 24) (rest := (finishActions.drop 22).take 2) run104 runTable
  have query1T : aT.state 1 = .shared (encodeWord left) :=
    (first3.retained_local_same_calls (index := 1) (by decide +kernel) (by decide +kernel)).trans query1
  obtain ⟨wl, al, runLeft, ml, rootsL, countL, frameL, view106, memoryL⟩ :=
    original_borrow_view_complete mt callee (finishCode 26) (slot := 1) (destination := 106) (by simp) (by decide)
      (place := .deref (.local 1)) rfl (by rw [query1T]; exact .shared _ [])
      (by simp [Partial.Locals.read, splitPlace, query1T, Slot.read, Slot.get, Slot.materialize_ofValue]) (.word left)
      (by rw [countT, count104]; omega) (by simpa [rootsT, roots104, Roots.set] using unbound 106 (by simp))
  have first5 : Calling.Prefix callee callers (finishCode 26) ((finishActions.drop 21).take 5) world active wl al :=
    Calling.Prefix.append (suffix := finishCode 26) (rest := (finishActions.drop 24).take 2) first3 runLeft
  have query2L : al.state 2 = .shared (encodeWord right) :=
    (first5.retained_local_same_calls (index := 2) (by decide +kernel) (by decide +kernel)).trans query2
  obtain ⟨wr, ar, runRight, mr, rootsR, countR, frameR, view107, memoryR⟩ :=
    original_borrow_view_complete ml callee (finishCode 28) (slot := 2) (destination := 107) (by simp) (by decide)
      (place := .deref (.local 2)) rfl (by rw [query2L]; exact .shared _ [])
      (by simp [Partial.Locals.read, splitPlace, query2L, Slot.read, Slot.get, Slot.materialize_ofValue]) (.word right)
      (by rw [countL, countT, count104]; omega)
      (by simpa [rootsL, rootsT, roots104, Roots.set] using unbound 107 (by simp))
  have first7 : Calling.Prefix callee callers (finishCode 28) ((finishActions.drop 21).take 7) world active wr ar :=
    Calling.Prefix.append (suffix := finishCode 28) (rest := (finishActions.drop 26).take 2) first5 runRight
  obtain ⟨w108, a108, run108, m108, roots108, count108, frame108, empty108, raw108, memory108⟩ :=
    original_open_local_complete mr callee (finishCode 29) (slot := 108) (by decide)
      (by rw [countR, countL, countT, count104]; omega)
      (by simpa [rootsR, rootsL, rootsT, roots104, Roots.set] using unbound 108 (by simp))
  obtain ⟨final, after, run109, machine, roots109, count109, frame109, empty109, raw109, memory109⟩ :=
    original_open_local_complete m108 callee (finishCode 30) (slot := 109) (by decide)
      (by rw [count108, countR, countL, countT, count104]; omega)
      (by simpa [roots108, rootsR, rootsL, rootsT, roots104, Roots.set] using unbound 109 (by simp))
  have last2 : Calling.Prefix callee callers (finishCode 30) ((finishActions.drop 28).take 2) wr ar final after :=
    Calling.Prefix.append (suffix := finishCode 30) (rest := [.storageLive 109]) run108 run109
  have whole : Calling.Prefix callee callers (finishCode 30) ((finishActions.drop 21).take 9) world active final after :=
    Calling.Prefix.append (suffix := finishCode 30) (rest := (finishActions.drop 28).take 2) first7 last2
  have afterMove : Calling.Prefix callee callers (finishCode 30) ((finishActions.drop 24).take 6) wt aT final after :=
    Calling.Prefix.append (suffix := finishCode 30) (rest := (finishActions.drop 26).take 4) runLeft
      (Calling.Prefix.append (suffix := finishCode 30) (rest := (finishActions.drop 28).take 2) runRight last2)
  have afterLeft : Calling.Prefix callee callers (finishCode 30) ((finishActions.drop 26).take 4) wl al final after :=
    Calling.Prefix.append (suffix := finishCode 30) (rest := (finishActions.drop 28).take 2) runRight last2
  have oldMemory : ∀ slot binding, active.roots slot = some binding → ∀ raw,
      world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw := by
    intro slot binding root raw read
    have outside : slot ∉ [104, 105, 106, 107, 108, 109] := by intro member; rw [unbound slot member] at root; cases root
    have different : slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 ∧ slot ≠ 109 := by simpa using outside
    have root104 : a104.roots slot = some binding := by simpa [roots104, Roots.set, different.1] using root
    have rootT : aT.roots slot = some binding := by simpa [rootsT, Roots.set, different.2.1] using root104
    have rootL : al.roots slot = some binding := by simpa [rootsL, Roots.set, different.2.2.1] using rootT
    have rootR : ar.roots slot = some binding := by simpa [rootsR, Roots.set, different.2.2.2.1] using rootL
    have root108 : a108.roots slot = some binding := by simpa [roots108, Roots.set, different.2.2.2.2.1] using rootR
    exact memory109 slot binding root108 raw (memory108 slot binding rootR raw (memoryR slot binding rootL raw
      (memoryL slot binding rootT raw (memoryT slot binding root104 raw (memory104 slot binding root raw read)))))
  have raw104T := memoryT 104 ⟨world.memory.length, world.memory.length⟩ (by simp [roots104, Roots.set]) _ raw104
  have raw104L := memoryL 104 ⟨world.memory.length, world.memory.length⟩ (by simp [rootsT, roots104, Roots.set]) _ raw104T
  have raw104R := memoryR 104 ⟨world.memory.length, world.memory.length⟩ (by simp [rootsL, rootsT, roots104, Roots.set]) _ raw104L
  have raw104A := memory108 104 ⟨world.memory.length, world.memory.length⟩ (by simp [rootsR, rootsL, rootsT, roots104, Roots.set]) _ raw104R
  have raw104F := memory109 104 ⟨world.memory.length, world.memory.length⟩ (by simp [roots108, rootsR, rootsL, rootsT, roots104, Roots.set]) _ raw104A
  refine ⟨final, after, whole, machine, count109.trans (count108.trans (countR.trans (countL.trans (countT.trans count104)))),
    frame109.trans (frame108.trans (frameR.trans (frameL.trans (frameT.trans frame104)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, oldMemory⟩
  · exact (afterMove.closed_local_same (index := 89) mt.native.valid mt.native.callersValid mt.native.wellFormed
      (by rw [empty89]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans empty89
  · exact (afterMove.closed_local_same (index := 105) mt.native.valid mt.native.callersValid mt.native.wellFormed
      (by rw [table105]; exact ofValue_typed (table_typed table)) (.adt .table) rfl (by decide +kernel)).trans table105
  · exact (afterLeft.retained_local_same_calls (index := 106) (by decide +kernel) (by decide +kernel)).trans view106
  · exact (last2.retained_local_same_calls (index := 107) (by decide +kernel) (by decide +kernel)).trans view107
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · refine ⟨?_, ⟨world.memory.length, world.memory.length⟩, ?_, raw104F⟩
      · have tail : Calling.Prefix callee callers (finishCode 30) ((finishActions.drop 22).take 8) w104 a104 final after :=
          Calling.Prefix.append (suffix := finishCode 30) (rest := (finishActions.drop 24).take 6) runTable afterMove
        exact (tail.closed_local_same (index := 104) m104.native.valid m104.native.callersValid m104.native.wellFormed
          (by rw [empty104]; exact .empty .u32) .u32 rfl (by decide +kernel)).trans empty104
      · simp [roots109, roots108, rootsR, rootsL, rootsT, roots104, Roots.set]
    · refine ⟨?_, ⟨wr.memory.length, wr.memory.length⟩, ?_, ?_⟩
      · exact (run109.closed_local_same (index := 108) m108.native.valid m108.native.callersValid m108.native.wellFormed
          (by rw [empty108]; exact .empty .u32) .u32 rfl (by decide)).trans empty108
      · simp [roots109, roots108, Roots.set]
      · exact memory109 108 _ (by simp [roots108, Roots.set]) _ raw108
    · exact ⟨empty109, ⟨w108.memory.length, w108.memory.length⟩, by simp [roots109, Roots.set], raw109⟩
  · intro slot outside
    have different : slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 ∧ slot ≠ 109 := by simpa using outside
    simp [roots109, roots108, rootsR, rootsL, rootsT, roots104, Roots.set,
      different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2]
  · intro slot member
    exact whole.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel)) h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  · intro slot outside unshared
    apply whole.unshared_local_same h.native.valid h.native.callersValid h.native.wellFormed unshared (by decide +kernel)
    have different : slot ≠ 89 ∧ slot ≠ 104 ∧ slot ≠ 105 ∧ slot ≠ 106 ∧ slot ≠ 107 ∧ slot ≠ 108 ∧ slot ≠ 109 := by simpa using outside
    simp [finishActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand,
      splitPlace, different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2.1, different.2.2.2.2.2.2]

end SubtreeProofs.Rust.SourceEval.Evaluator
