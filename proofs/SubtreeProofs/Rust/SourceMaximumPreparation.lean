module

public import SubtreeProofs.Rust.SourceMaximumEntry
public import SubtreeProofs.Rust.SourceOriginalOpenLocal
public import SubtreeProofs.Rust.SourceOriginalBorrowView
public import SubtreeProofs.Rust.SourceOriginalConstantView
public import SubtreeProofs.Rust.SourcePrefixMaskFacts
public import SubtreeProofs.Rust.SourceFreshWritePrefixes

/-! Construct all eight actual public preparation actions. Shared query views
retain original loan origins, empty result/return storage retains its bytes,
and the cold table is constructed through its real guarded assignment. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def callCode : Code := .step evaluateCall (afterCall.foldr Control.Tree.step .ret)
def prepareCode (index : Nat) : Code := (beforeCall.drop index).foldr Control.Tree.step callCode

theorem body_preparation : body = beforeCall.foldr Control.Tree.step callCode := by
  simp only [body, List.foldr_append]
  rfl

theorem preparation_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2] world active)
    (callee : Derived.Callees) (count : 7 ≤ active.count) (left right : BalancedWord)
    (first : active.state 1 = .shared (encodeWord left)) (second : active.state 2 = .shared (encodeWord right))
    (unbound : ∀ slot ∈ [0, 3, 4, 5, 6], active.roots slot = none) :
    ∃ final after returnRoot resultRoot,
      Calling.Prefix callee callers callCode beforeCall world active final after ∧
      OriginalLoanMachine before callers previous external [5, 4, 1, 2] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.roots 0 = some returnRoot ∧ after.roots 3 = some resultRoot ∧
      final.memory[returnRoot.address]? = some (.node .tuple 0 []) ∧
      final.memory[resultRoot.address]? = some (.node .tuple 0 []) ∧
      after.state 0 = .empty ∧ after.state 3 = .empty ∧
      after.state 4 = .shared (encodeWord left) ∧ after.state 5 = .shared (encodeWord right) ∧
      after.state 6 = Slot.ofValue (encodeTable .Empty) ∧
      (∀ slot, slot ∉ [0, 3, 4, 5, 6] → after.roots slot = active.roots slot) := by
  obtain ⟨w0, a0, run0, m0, roots0, count0, frame0, empty0, raw0, memory0⟩ :=
    original_open_local_complete h callee (prepareCode 1) (slot := 0) (by decide) (by omega) (unbound 0 (by simp))
  obtain ⟨w3, a3, run3, m3, roots3, count3, frame3, empty3, raw3, memory3⟩ :=
    original_open_local_complete m0 callee (prepareCode 2) (slot := 3) (by decide)
      (by rw [count0]; omega) (by simpa [roots0, Roots.set] using unbound 3 (by simp))
  have opened : Calling.Prefix callee callers (prepareCode 2) (beforeCall.take 2) world active w3 a3 :=
    Calling.Prefix.append (suffix := prepareCode 2) (rest := [.storageLive 3]) run0 run3
  have left3 : a3.state 1 = .shared (encodeWord left) :=
    (opened.retained_local_same_calls (index := 1) (by decide +kernel) (by decide +kernel)).trans first
  obtain ⟨wl, al, runLeft, ml, rootsL, countL, frameL, view4, memoryL⟩ :=
    original_borrow_view_complete m3 callee (prepareCode 4) (slot := 1) (destination := 4) (by simp) (by decide)
      (place := .deref (.local 1)) rfl (by rw [left3]; exact .shared _ [])
      (by simp [Partial.Locals.read, splitPlace, left3, Slot.read, Slot.get, Slot.materialize_ofValue]) (.word left)
      (by rw [count3, count0]; omega) (by simpa [roots3, roots0, Roots.set] using unbound 4 (by simp))
  have first4 : Calling.Prefix callee callers (prepareCode 4) (beforeCall.take 4) world active wl al :=
    Calling.Prefix.append (suffix := prepareCode 4) (rest := (beforeCall.drop 2).take 2) opened runLeft
  have rightL : al.state 2 = .shared (encodeWord right) :=
    (first4.retained_local_same_calls (index := 2) (by decide +kernel) (by decide +kernel)).trans second
  obtain ⟨wr, ar, runRight, mr, rootsR, countR, frameR, view5, memoryR⟩ :=
    original_borrow_view_complete ml callee (prepareCode 6) (slot := 2) (destination := 5) (by simp) (by decide)
      (place := .deref (.local 2)) rfl (by rw [rightL]; exact .shared _ [])
      (by simp [Partial.Locals.read, splitPlace, rightL, Slot.read, Slot.get, Slot.materialize_ofValue]) (.word right)
      (by rw [countL, count3, count0]; omega)
      (by simpa [rootsL, roots3, roots0, Roots.set] using unbound 5 (by simp))
  have first6 : Calling.Prefix callee callers (prepareCode 6) (beforeCall.take 6) world active wr ar :=
    Calling.Prefix.append (suffix := prepareCode 6) (rest := (beforeCall.drop 4).take 2) first4 runRight
  obtain ⟨final, after, runTable, machine, rootsT, countT, frameT, table6, memoryT⟩ :=
    original_constant_view_complete mr callee callCode (destination := 6) (by decide) .table 0
      (table_typed .Empty) (.adt .table) (by rw [countR, countL, count3, count0]; omega)
      (by simpa [rootsR, rootsL, roots3, roots0, Roots.set] using unbound 6 (by simp))
  have whole : Calling.Prefix callee callers callCode beforeCall world active final after :=
    Calling.Prefix.append (suffix := callCode) (rest := (beforeCall.drop 6)) first6 runTable
  have old0 : a0.roots 0 = some ⟨world.memory.length, world.memory.length⟩ := by simp [roots0, Roots.set]
  have at3_0 : a3.roots 0 = some ⟨world.memory.length, world.memory.length⟩ := by simp [roots3, Roots.set, old0]
  have atL_0 : al.roots 0 = some ⟨world.memory.length, world.memory.length⟩ := by simp [rootsL, Roots.set, at3_0]
  have atR_0 : ar.roots 0 = some ⟨world.memory.length, world.memory.length⟩ := by simp [rootsR, Roots.set, atL_0]
  have at3_3 : a3.roots 3 = some ⟨w0.memory.length, w0.memory.length⟩ := by simp [roots3, Roots.set]
  have atL_3 : al.roots 3 = some ⟨w0.memory.length, w0.memory.length⟩ := by simp [rootsL, Roots.set, at3_3]
  have atR_3 : ar.roots 3 = some ⟨w0.memory.length, w0.memory.length⟩ := by simp [rootsR, Roots.set, atL_3]
  have last6 : Calling.Prefix callee callers callCode (beforeCall.drop 2) w3 a3 final after :=
    Calling.Prefix.append (suffix := callCode) (rest := beforeCall.drop 4)
      runLeft (Calling.Prefix.append (suffix := callCode) (rest := beforeCall.drop 6) runRight runTable)
  have last4 : Calling.Prefix callee callers callCode (beforeCall.drop 4) wl al final after :=
    Calling.Prefix.append (suffix := callCode) (rest := beforeCall.drop 6) runRight runTable
  refine ⟨final, after, ⟨world.memory.length, world.memory.length⟩, ⟨w0.memory.length, w0.memory.length⟩,
    whole, machine, countT.trans (countR.trans (countL.trans (count3.trans count0))),
    frameT.trans (frameR.trans (frameL.trans (frame3.trans frame0))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, table6, ?_⟩
  · simp [rootsT, Roots.set, atR_0]
  · simp [rootsT, Roots.set, atR_3]
  · exact memoryT 0 _ atR_0 _ (memoryR 0 _ atL_0 _ (memoryL 0 _ at3_0 _ (memory3 0 _ old0 _ raw0)))
  · exact memoryT 3 _ atR_3 _ (memoryR 3 _ atL_3 _ (memoryL 3 _ at3_3 _ raw3))
  · exact last6.empty_untouched (run3.empty_untouched empty0 (by decide)) (by decide)
  · exact last6.empty_untouched empty3 (by decide)
  · exact (last4.retained_local_same_calls (index := 4) (by decide +kernel) (by decide +kernel)).trans view4
  · exact (runTable.retained_local_same_calls (index := 5) (by decide +kernel) (by decide +kernel)).trans view5
  · intro slot outside
    have h0 : slot ≠ 0 := by intro same; subst slot; simp at outside
    have h3 : slot ≠ 3 := by intro same; subst slot; simp at outside
    have h4 : slot ≠ 4 := by intro same; subst slot; simp at outside
    have h5 : slot ≠ 5 := by intro same; subst slot; simp at outside
    have h6 : slot ≠ 6 := by intro same; subst slot; simp at outside
    simp only [rootsT, rootsR, rootsL, roots3, roots0, Roots.set, h0, h3, h4, h5, h6, ite_false]

end SubtreeProofs.Rust.SourceEval.Maximum
