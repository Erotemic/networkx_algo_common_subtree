import SubtreeProofs.Rust.SourcePairChoices

/-! All score orders and ties execute the real two-choice parent region.
Distinct input word shapes expose which candidate wins through its owner count;
two older external Boxes remain live and outside every selected owner inventory. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SourceParentChoicesTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def older : World := ⟨[.node .word 0 [], .node .word 0 []],
  fun a => if a < 2 then some .box else none, fun a => decide (a < 2)⟩
private def heap : World := ⟨[
  .node .word 0 [], .node .word 0 [], .node .word 0 [], .node .word 0 [],
  .node .word 0 [], .node .word 1 [.owned 6, .owned 7], .node .word 0 [], .node .word 0 [],
  .node .word 1 [.owned 9, .owned 10], .node .word 0 [], .node .word 0 [],
  .node .word 1 [.owned 12, .owned 13], .node .word 0 [], .node .word 0 []],
  fun a => if a < 14 then some .box else none, fun a => decide (a < 14)⟩
private def first (score : Aeneas.Std.U32) : CommonEmbedding := ⟨.Pair .Empty .Empty, score⟩
private def second (score : Aeneas.Std.U32) : CommonEmbedding := ⟨.Pair .Empty (.Pair .Empty .Empty), score⟩
private def third (score : Aeneas.Std.U32) : CommonEmbedding := ⟨.Pair (.Pair .Empty .Empty) (.Pair .Empty .Empty), score⟩
private def packets (a b c : Aeneas.Std.U32) : List ValueCell :=
  [(.node .embedding 0 [.node .word 1 [.owned 2, .owned 3], .number a.val], encodeResult (first a)),
   (.node .embedding 0 [.node .word 1 [.owned 4, .owned 5], .number b.val], encodeResult (second b)),
   (.node .embedding 0 [.node .word 1 [.owned 8, .owned 11], .number c.val], encodeResult (third c))]
private def inputOwners : List Nat := [2, 3, 4, 6, 7, 5, 9, 10, 8, 12, 13, 11]
private def entered (a b c : Aeneas.Std.U32) := heap.stackCells 200 ((packets a b c).map Prod.fst)
private def initial (a b c : Aeneas.Std.U32) := initialActivation heap 200 113 (packets a b c)
private def prepActions : List SourceEval.Action :=
  [.storageLive 64, .assign 64 (.use (.move (.local 1))), .storageLive 81, .assign 81 (.use (.move (.local 2))),
   .storageLive 95, .assign 95 (.use (.move (.local 3)))]
private def prepCode (index : Nat) := (prepActions.drop index).foldr Control.Tree.step (SourceEval.Evaluator.finishCode 6)

private theorem older_wf : older.WellFormed := by simp [World.WellFormed, older]
private theorem heap_wf : heap.WellFormed := by simp [World.WellFormed, heap]
private theorem heap_kept : Preserves older heap [] := by
  refine ⟨by simp [Retains], ?_, by simp⟩
  intro address kind classified
  simp [older] at classified
  have large : address < 14 := by omega
  simpa [heap, large] using classified.2

private theorem input_footprint (a b c : Aeneas.Std.U32) :
    FieldsFootprint heap.memory ((packets a b c).map Prod.fst) inputOwners := by
  refine .cons (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number _) .nil)))
    (.cons (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl
      (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))) (.cons (.number _) .nil)))
      (.cons (.node (.cons (.node (.cons (.owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))))
        (.cons (.owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil)))
        (.cons (.number _) .nil))) .nil))

private theorem input_readable (a b c : Aeneas.Std.U32) :
    ∀ p ∈ packets a b c, Readable heap.memory heap.live p.1 p.2 := by
  intro p member
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨[2, 3], .node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil)), by simp [AliveOn, heap]⟩
  · exact ⟨[4, 6, 7, 5], .node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl
      (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil)))
      (.cons (.number _) .nil)), by simp [AliveOn, heap]⟩
  · exact ⟨[9, 10, 8, 12, 13, 11], .node (.cons (.node (.cons
      (.owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))))
      (.cons (.owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil)))
      (.cons (.number _) .nil)), by simp [AliveOn, heap]⟩

private theorem input_resources : OwnerFrame heap (inputOwners ++ [0, 1]) ∧ BoxCoverage heap (inputOwners ++ [0, 1]) := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 14 := by simp only [inputOwners, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [heap, bound]
  · intro address member
    have bound : address < 14 := by simp only [inputOwners, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [heap, bound]
  · intro address classified _
    have bound : address < 14 := by simpa [heap] using classified
    simp only [inputOwners, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    omega

private theorem initial_other_empty (a b c : Aeneas.Std.U32) (slot : Nat) (one : slot ≠ 1) (two : slot ≠ 2) (three : slot ≠ 3) :
    (initial a b c).state slot = .empty := by
  by_cases zero : slot = 0
  · subst slot; rfl
  · have high : 3 ≤ slot - 1 := by omega
    have missing : (packets a b c)[slot - 1]? = none := List.getElem?_eq_none (by simp [packets]; omega)
    simp only [initial, initialActivation, SourceEval.initialState, Partial.Locals.lift, initialEnv, zero, ite_false,
      List.getElem?_map, missing, Option.map_none]

private theorem initial_closed (a b c : Aeneas.Std.U32) : ClosedState (initial a b c).state := by
  intro slot
  by_cases one : slot = 1
  · subst slot; exact ⟨.adt .embedding, ofValue_typed (result_typed (first a)), .adt .embedding⟩
  · by_cases two : slot = 2
    · subst slot; exact ⟨.adt .embedding, ofValue_typed (result_typed (second b)), .adt .embedding⟩
    · by_cases three : slot = 3
      · subst slot; exact ⟨.adt .embedding, ofValue_typed (result_typed (third c)), .adt .embedding⟩
      · exact ⟨.u32, by rw [initial_other_empty a b c slot one two three]; exact .empty _, .u32⟩

private theorem constructed (a b c : Aeneas.Std.U32) : ∃ (final : World) (after : Activation) (resources : Resources),
    after.state 99 = Slot.ofValue (encodeResult (SourceEval.Evaluator.selectedWitness (first a) (second b) (third c))) ∧
    LocalResources final after.frame after.roots after.state 99 resources ∧
    (∀ address ∈ resources.owners, 2 ≤ address) ∧
    resources.owners.length = (Slot.ofValue (encodeResult (SourceEval.Evaluator.selectedWitness (first a) (second b) (third c)))).dropWork.boxes ∧
    final.live 0 = true ∧ final.live 1 = true := by
  have valid := initialActivation_valid heap_wf 200 113 (input_readable a b c) (by simp [packets])
  have entry := (enter_complete heap_wf 200 113 (input_readable a b c) (by simp [packets])).1
  have resources := enter_owner_resources heap_wf 200 113 (callers := []) (external := [0, 1]) (by simp)
    (input_readable a b c) (input_footprint a b c)
    (by simpa [callerOwners] using input_resources.1) (by simpa [callerOwners] using input_resources.2) entry
  have machine : OriginalLoanMachine older [] {} [0, 1] [] (entered a b c) (initial a b c) := by
    refine ⟨⟨older_wf, .nil, heap_kept.trans (heap.stackCells_keeps heap_wf 200 _ []).preserves,
      valid, heap_wf.stackCells _ _, ?_, ?_, ?_, ?_, resources.1, resources.2⟩,
      (fun slot _ => initial_closed a b c slot), by simp, by simp⟩
    · intro _ _ _ caller member; cases member
    · simp [older, entered, World.stackCells, heap]
    · intro slot binding root
      simp only [initial, initialActivation, argumentRoots] at root
      split at root
      next ready => cases root; change 2 ≤ 14 + (slot - 1); omega
      next => cases root
    · intro slot
      obtain ⟨ty, typed, shape⟩ := initial_closed a b c slot
      exact LoanSafe.of_closed typed shape
  have own : (initial a b c).owners (entered a b c) = inputOwners := by
    change (initialActivation heap 200 113 (packets a b c)).owners (heap.stackCells 200 ((packets a b c).map Prod.fst)) = inputOwners
    rw [initialActivation_owners _ _ (input_readable a b c) (by simp [packets]), packetOwners_unique (input_readable a b c) (input_footprint a b c)]
  have above : ∀ slot, slot < (initial a b c).count → LocalOwnersAbove older.memory.length (entered a b c) (initial a b c) slot := by
    intro slot bound represented localResource address member
    have partition := (initial a b c).owners_partition (entered a b c) slot bound localResource.source.ownerList
    have owned := partition.symm.subset (List.mem_append_left _ member)
    rw [own] at owned
    change 2 ≤ address
    simp only [inputOwners, List.mem_cons, List.not_mem_nil, or_false] at owned
    omega
  let callee := Helpers.callee 0 0
  obtain ⟨w1, a1, p1, m1, r1, c1, _, e1, v64, _⟩ := original_move_view_complete machine callee (prepCode 2)
    (source := 1) (destination := 64) (by simp) (by simp) (by rfl) (result_typed (first a)) (.adt .embedding) (by change 64 < 113; decide) (by rfl)
  have value2 : a1.state 2 = Slot.ofValue (encodeResult (second b)) :=
    p1.closed_local_same (index := 2) machine.native.valid machine.native.callersValid machine.native.wellFormed
      (ofValue_typed (result_typed (second b))) (.adt .embedding) rfl (by decide)
  obtain ⟨w2, a2, p2, m2, r2, c2, _, e2, v81, _⟩ := original_move_view_complete m1 callee (prepCode 4)
    (source := 2) (destination := 81) (by simp) (by simp) value2 (result_typed (second b)) (.adt .embedding)
    (by rw [c1]; change 81 < 113; decide) (by simp [r1, initial, initialActivation, argumentRoots, Roots.set, packets])
  have first4 : Calling.Prefix callee [] (prepCode 4) (prepActions.take 4) (entered a b c) (initial a b c) w2 a2 :=
    Calling.Prefix.append (suffix := prepCode 4) (rest := prepActions.drop 2 |>.take 2) p1 p2
  have value3 : a2.state 3 = Slot.ofValue (encodeResult (third c)) :=
    first4.closed_local_same (index := 3) machine.native.valid machine.native.callersValid machine.native.wellFormed
      (ofValue_typed (result_typed (third c))) (.adt .embedding) rfl (by decide)
  obtain ⟨wp, ap, p3, mp, r3, c3, _, e3, v95, _⟩ := original_move_view_complete m2 callee (SourceEval.Evaluator.finishCode 6)
    (source := 3) (destination := 95) (by simp) (by simp) value3 (result_typed (third c)) (.adt .embedding)
    (by rw [c2, c1]; change 95 < 113; decide) (by simp [r2, r1, initial, initialActivation, argumentRoots, Roots.set, packets])
  have last4 : Calling.Prefix callee [] (SourceEval.Evaluator.finishCode 6) (prepActions.drop 2) w1 a1 wp ap :=
    Calling.Prefix.append (suffix := SourceEval.Evaluator.finishCode 6) (rest := prepActions.drop 4) p2 p3
  have prep : Calling.Prefix callee [] (SourceEval.Evaluator.finishCode 6) prepActions (entered a b c) (initial a b c) wp ap :=
    Calling.Prefix.append (suffix := SourceEval.Evaluator.finishCode 6) (rest := prepActions.drop 2) p1 last4
  have empty1 : ap.state 1 = .empty :=
    (last4.closed_local_same (index := 1) m1.native.valid m1.native.callersValid m1.native.wellFormed
      (by rw [e1]; exact .empty .u32) .u32 rfl (by decide)).trans e1
  have empty2 : ap.state 2 = .empty :=
    (p3.closed_local_same (index := 2) m2.native.valid m2.native.callersValid m2.native.wellFormed
      (by rw [e2]; exact .empty .u32) .u32 rfl (by decide)).trans e2
  have emptyOther : ∀ slot, slot ∉ [1, 2, 3, 64, 81, 95] → ap.state slot = .empty := by
    intro slot outside
    have diff : slot ≠ 1 ∧ slot ≠ 2 ∧ slot ≠ 3 ∧ slot ≠ 64 ∧ slot ≠ 81 ∧ slot ≠ 95 := by simpa using outside
    have old := initial_other_empty a b c slot diff.1 diff.2.1 diff.2.2.1
    exact (prep.closed_local_same (index := slot) machine.native.valid machine.native.callersValid machine.native.wellFormed
      (by rw [old]; exact .empty .u32) .u32 rfl (by simp [prepActions, SourceEval.LocalPreservation.action, SourceEval.LocalPreservation.expression,
        SourceEval.LocalPreservation.operand, Partial.splitPlace, diff.1, diff.2.1, diff.2.2.1, diff.2.2.2.1, diff.2.2.2.2.1, diff.2.2.2.2.2])).trans old
  have familyEmpty : ∀ slot ∈ [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13], ap.state slot = .empty := by
    intro slot member
    by_cases one : slot = 1
    · subst slot; exact empty1
    · by_cases two : slot = 2
      · subst slot; exact empty2
      · apply emptyOther
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have parent : OriginalLoanMachine older [] {} [0, 1] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] wp ap := by
    refine ⟨mp.native, fun slot _ => mp.closed slot (by simp), ?_, ?_⟩
    · intro slot member; rw [familyEmpty slot member]; simp only [Slot.dropWork]
    · intro slot member
      exact LoanOrigin.of_closed mp.native.valid older.memory.length slot (by rw [familyEmpty slot member]; exact .empty .u32) .u32
  have native64 : ap.state 64 = Slot.ofValue (encodeResult (first a)) :=
    (last4.closed_local_same (index := 64) m1.native.valid m1.native.callersValid m1.native.wellFormed
      (by rw [v64]; exact ofValue_typed (result_typed _)) (.adt .embedding) rfl (by decide)).trans v64
  have native81 : ap.state 81 = Slot.ofValue (encodeResult (second b)) :=
    (p3.closed_local_same (index := 81) m2.native.valid m2.native.callersValid m2.native.wellFormed
      (by rw [v81]; exact ofValue_typed (result_typed _)) (.adt .embedding) rfl (by decide)).trans v81
  have plan1 : OwnerTransfer 1 prepActions 64 := .keep rfl (by decide) (.assign (fun _ _ _ h => OperandSourcesAbove.single_move h rfl)
    (.keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide) (.nil 64))))))
  have plan2 : OwnerTransfer 2 prepActions 81 := .keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide)
    (.assign (fun _ _ _ h => OperandSourcesAbove.single_move h rfl) (.keep rfl (by decide) (.keep rfl (by decide) (.nil 81))))))
  have plan3 : OwnerTransfer 3 prepActions 95 := .keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide)
    (.keep rfl (by decide) (.assign (fun _ _ _ h => OperandSourcesAbove.single_move h rfl) (.nil 95))))))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, final, after, finalMachine, selected, _, _, _, _, _, fresh, _, _, _, _, _⟩ :=
    SourceEval.Evaluator.pair_choices_complete parent (first a) (second b) (third c) native64 native81 v95
      (prep.owner_transfer plan1 machine.native.valid machine.native.callersValid machine.native.wellFormed (above 1 (by change 1 < 113; decide)))
      (prep.owner_transfer plan2 machine.native.valid machine.native.callersValid machine.native.wellFormed (above 2 (by change 2 < 113; decide)))
      (prep.owner_transfer plan3 machine.native.valid machine.native.callersValid machine.native.wellFormed (above 3 (by change 3 < 113; decide)))
      (by
        intro slot member
        apply LocalOwnersAbove.of_zero
        have outside : slot ∉ [1, 2, 3, 64, 81, 95] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> decide
        change (ap.state slot).dropWork.boxes = 0
        rw [emptyOther slot outside]; simp only [Slot.dropWork])
      (by rw [c3, c2, c1]; change 104 ≤ 113; decide)
      (by intro slot member; rw [r3, r2, r1]
          have diff : slot ≠ 64 ∧ slot ≠ 81 ∧ slot ≠ 95 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
          simp [Roots.set, diff.1, diff.2.1, diff.2.2, initial, initialActivation, argumentRoots, packets]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
  obtain ⟨_, frame⟩ := finalMachine.native.valid.2
  obtain ⟨output, _, represented⟩ := frame.inspectSlot 99
  have count := represented.boxes
  rw [selected] at count
  exact ⟨final, after, output, selected, represented, fresh output represented, count,
    finalMachine.native.ownerFrame.alive 0 (by simp [callerOwners]), finalMachine.native.ownerFrame.alive 1 (by simp [callerOwners])⟩

-- First candidate wins, middle candidate wins, last candidate wins, and ties
-- retain the first input. Different word shapes expose the selected branch.
example : ∃ (final : World) (after : Activation) (resources : Resources), LocalResources final after.frame after.roots after.state 99 resources ∧ resources.owners.length = 2 := by
  obtain ⟨final, after, resources, _, represented, _, count, _, _⟩ := constructed 10#u32 7#u32 3#u32
  exact ⟨final, after, resources, represented, count.trans (by with_unfolding_all rfl)⟩
example : ∃ (final : World) (after : Activation) (resources : Resources), LocalResources final after.frame after.roots after.state 99 resources ∧ resources.owners.length = 4 := by
  obtain ⟨final, after, resources, _, represented, _, count, _, _⟩ := constructed 7#u32 10#u32 3#u32
  exact ⟨final, after, resources, represented, count.trans (by with_unfolding_all rfl)⟩
example : ∃ (final : World) (after : Activation) (resources : Resources), LocalResources final after.frame after.roots after.state 99 resources ∧ resources.owners.length = 6 := by
  obtain ⟨final, after, resources, _, represented, _, count, _, _⟩ := constructed 7#u32 3#u32 10#u32
  exact ⟨final, after, resources, represented, count.trans (by with_unfolding_all rfl)⟩
example : ∃ (final : World) (after : Activation) (resources : Resources), LocalResources final after.frame after.roots after.state 99 resources ∧ resources.owners.length = 2 := by
  obtain ⟨final, after, resources, _, represented, _, count, _, _⟩ := constructed 7#u32 7#u32 7#u32
  exact ⟨final, after, resources, represented, count.trans (by with_unfolding_all rfl)⟩

end SourceParentChoicesTests
