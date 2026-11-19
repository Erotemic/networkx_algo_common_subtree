import SubtreeProofs.Rust.SourcePairReturnRetirement
import SubtreeProofs.Rust.SourceFreshRetirement

/-! Output assembly retains a shared tuple alias into the old table while
moving its two old owners beside a six-owner fresh witness. Witness provenance
is a field property of the resulting eight-owner tuple. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SourceParentOutputTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def oldEntry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [], .node .embedding 0 [.node .word 0 [], .number 0]]
private def older : World := ⟨[oldEntry, .node .table 0 []], fun a => if a < 2 then some .box else none, fun a => decide (a < 2)⟩
private def heap : World := ⟨[oldEntry, .node .table 0 [], .node .word 1 [.owned 3, .owned 4],
  .node .word 0 [], .node .word 0 [], .node .word 1 [.owned 6, .owned 7], .node .word 0 [], .node .word 0 []],
  fun a => if a < 8 then some .box else none, fun a => decide (a < 8)⟩
private def answer : CommonEmbedding := ⟨.Pair (.Pair .Empty .Empty) (.Pair .Empty .Empty), 9#u32⟩
private def memo : MemoTable := .Entry ⟨.Empty, .Empty, ⟨.Empty, 0#u32⟩⟩ .Empty
private def tableCell : Cell := .node .table 1 [.owned 0, .owned 1]
private def selectedCell : Cell := .node .embedding 0 [.node .word 1 [.owned 2, .owned 5], .number 9]
private def tupleCell : Cell := .node .tuple 0 [.shared ⟨0, [0]⟩, .shared ⟨0, [1]⟩]
private def tupleValue : Value := .node .tuple 0 [.reference (encodeWord .Empty), .reference (encodeWord .Empty)]
private def packets : List ValueCell := [(tableCell, encodeTable memo), (selectedCell, encodeResult answer),
  (.number 0, .number 0), (.number 0, .number 0), (.number 0, .number 0), (.number 0, .number 0),
  (.number 0, .number 0), (.number 0, .number 0), (.number 0, .number 0), (.number 0, .number 0),
  (.number 0, .number 0), (.number 0, .number 0), (tupleCell, tupleValue)]
private def owners : List Nat := [0, 1, 3, 4, 2, 6, 7, 5]
private def entered := heap.stackCells 200 (packets.map Prod.fst)
private def initial := initialActivation heap 200 113 packets
private def prepActions : List SourceEval.Action := [.storageLive 104, .assign 104 (.use (.move (.local 1))),
  .storageLive 99, .assign 99 (.use (.move (.local 2))), .storageLive 0]
private def prepCode (i : Nat) := (prepActions.drop i).foldr Control.Tree.step (SourceEval.Evaluator.finishCode 39)

private theorem heap_wf : heap.WellFormed := by simp [heap, World.WellFormed]
private theorem old_wf : older.WellFormed := by simp [older, World.WellFormed]
private theorem old_kept : Preserves older heap [] := by
  refine ⟨by simp [Retains], ?_, by simp⟩
  intro address kind classified
  simp [older] at classified
  have small : address < 8 := by omega
  simpa [heap, small] using classified.2

private theorem entry_graph : Graph heap.memory oldEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult ⟨.Empty, 0#u32⟩]) [] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons (.node .nil) (.cons (.number 0) .nil))) .nil)))
private theorem selected_graph : Graph heap.memory selectedCell (encodeResult answer) [3, 4, 2, 6, 7, 5] := by
  have left : Graph heap.memory (.owned 2) (.boxed (encodeWord (.Pair .Empty .Empty))) [3, 4, 2] :=
    .owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
  have right : Graph heap.memory (.owned 5) (.boxed (encodeWord (.Pair .Empty .Empty))) [6, 7, 5] :=
    .owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
  exact .node (.cons (.node (.cons left (.cons right .nil))) (.cons (.number 9) .nil))
private theorem selected_footprint : Footprint heap.memory selectedCell [3, 4, 2, 6, 7, 5] := by
  have left : Footprint heap.memory (.owned 2) [3, 4, 2] :=
    .owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
  have right : Footprint heap.memory (.owned 5) [6, 7, 5] :=
    .owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
  exact .node (.cons (.node (.cons left (.cons right .nil))) (.cons (.number 9) .nil))
private theorem tuple_graph : Graph heap.memory tupleCell tupleValue [0, 0] :=
  .node (.cons (.shared rfl (.node .nil)) (.cons (.shared rfl (.node .nil)) .nil))
private theorem input_readable : ∀ p ∈ packets, Readable heap.memory heap.live p.1 p.2 := by
  intro p member
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨[0, 1], .node (.cons (.owned rfl entry_graph) (.cons (.owned rfl (.node .nil)) .nil)), by simp [AliveOn, heap]⟩
  · exact ⟨_, selected_graph, by simp [AliveOn, heap]⟩
  all_goals first | exact ⟨[], .number 0, by simp [AliveOn]⟩ | exact ⟨_, tuple_graph, by simp [AliveOn, heap]⟩
private theorem input_footprint : FieldsFootprint heap.memory (packets.map Prod.fst) owners := by
  have entryFoot : Footprint heap.memory oldEntry [] :=
    .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons (.node .nil) (.cons (.number 0) .nil))) .nil)))
  have tableFoot : Footprint heap.memory tableCell [0, 1] :=
    .node (.cons (.owned rfl entryFoot) (.cons (.owned rfl (.node .nil)) .nil))
  refine .cons tableFoot (.cons selected_footprint ?_)
  iterate 10 refine .cons (.number 0) ?_
  exact .cons (.node (.cons (.shared _) (.cons (.shared _) .nil))) .nil
private theorem input_resources : OwnerFrame heap owners ∧ BoxCoverage heap owners := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have small : address < 8 := by simp only [owners, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [heap, small]
  · intro address member
    have small : address < 8 := by simp only [owners, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [heap, small]
  · intro address classified _
    have small : address < 8 := by simpa [heap] using classified
    simp only [owners, List.mem_cons, List.not_mem_nil, or_false]; omega
private theorem initial_high_empty (slot : Nat) (high : 13 < slot) : initial.state slot = .empty := by
  have absent : packets[slot - 1]? = none := List.getElem?_eq_none (by simp [packets]; omega)
  simp only [initial, initialActivation, SourceEval.initialState, Partial.Locals.lift, initialEnv,
    show slot ≠ 0 by omega, ite_false, List.getElem?_map, absent, Option.map_none]
private theorem initial_tuple : initial.state 13 = SourceEval.Evaluator.queryTuple .Empty .Empty := by
  with_unfolding_all rfl
private theorem initial_closed : ClosedOutside [13] initial.state := by
  intro slot outside
  by_cases high : 13 < slot
  · exact ⟨.u32, by rw [initial_high_empty slot high]; exact .empty _, .u32⟩
  · have small : slot ≤ 13 := by omega
    interval_cases slot <;> first
      | exact ⟨.adt .table, ofValue_typed (table_typed memo), .adt .table⟩
      | exact ⟨.adt .embedding, ofValue_typed (result_typed answer), .adt .embedding⟩
      | with_unfolding_all exact ⟨.u32, .number (by decide), .u32⟩
      | exact ⟨.u32, .empty _, .u32⟩
      | exact False.elim (outside (by decide))

example : ∃ start startActive final after resources,
    OriginalLoanMachine older [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    after.state 0 = Slot.ofValue (SourceEval.Evaluator.encodeOutput (some answer) memo) ∧
    LocalResultOwnersAbove 2 final after 0 ∧
    LocalResources final after.frame after.roots after.state 0 resources ∧ resources.owners.length = 8 ∧
    after.state 13 = SourceEval.Evaluator.queryTuple .Empty .Empty ∧
    (∀ slot ∈ [99, 104, 110, 111, 112], after.state slot = .empty ∧ after.roots slot = none) ∧
    Calling.Prefix (Helpers.callee 0 0) [] (SourceEval.Evaluator.finishCode 56)
      ((SourceEval.Evaluator.finishActions.drop 39).take 17) start startActive final after := by
  have valid := initialActivation_valid heap_wf 200 113 input_readable (by simp [packets])
  have entry := (enter_complete heap_wf 200 113 input_readable (by simp [packets])).1
  have resources := enter_owner_resources heap_wf 200 113 (callers := []) (external := []) (by simp)
    input_readable input_footprint (by simpa [callerOwners] using input_resources.1)
    (by simpa [callerOwners] using input_resources.2) entry
  obtain ⟨_, frame⟩ := valid.2
  obtain ⟨r13, scan13, rep13⟩ := frame.inspectSlot 13
  have measured13 : (inspectSlot entered 200 initial.roots initial.state 13).map Resources.loans = some [0, 0] := by decide +kernel
  change inspectSlot entered 200 initial.roots initial.state 13 = some r13 at scan13
  rw [scan13] at measured13
  have loans13 := Option.some.inj measured13
  have origin13 : LoanOrigin entered initial 2 13 := by
    refine ⟨r13, rep13, ?_⟩
    intro address member
    rw [loans13] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
  have machine : OriginalLoanMachine older [] {} [] [13] entered initial := by
    refine ⟨⟨old_wf, .nil, old_kept.trans (heap.stackCells_keeps heap_wf 200 _ []).preserves,
      valid, heap_wf.stackCells _ _, ?_, ?_, ?_, ?_, resources.1, resources.2⟩, initial_closed, ?_, ?_⟩
    · intro _ _ _ caller member; cases member
    · simp [older, entered, World.stackCells, heap]
    · intro slot binding root
      simp only [initial, initialActivation, argumentRoots] at root
      split at root
      next bound => cases root; change 2 ≤ 8 + (slot - 1); omega
      next => cases root
    · intro slot
      by_cases thirteen : slot = 13
      · subst slot
        rw [initial_tuple]
        change LoanSafe (.node .tuple 0 [.shared (encodeWord .Empty), .shared (encodeWord .Empty)])
        exact .node (.cons (.shared (.word .Empty)) (.cons (.shared (.word .Empty)) .nil))
      · obtain ⟨ty, typed, closed⟩ := initial_closed slot (by simpa using thirteen)
        exact LoanSafe.of_closed typed closed
    · intro slot member
      have same : slot = 13 := by simpa using member
      subst slot
      rw [initial_tuple]
      simp [SourceEval.Evaluator.queryTuple, Slot.dropWork, dropFields, DropWork.plus]
    · intro slot member
      have same : slot = 13 := by simpa using member
      subst slot
      exact origin13
  obtain ⟨r2, scan2, rep2⟩ := frame.inspectSlot 2
  have measured2 : (inspectSlot entered 200 initial.roots initial.state 2).map Resources.owners = some [3, 4, 2, 6, 7, 5] := by decide +kernel
  change inspectSlot entered 200 initial.roots initial.state 2 = some r2 at scan2
  rw [scan2] at measured2
  have owners2 := Option.some.inj measured2
  have fresh2 : LocalOwnersAbove 2 entered initial 2 := LocalOwnersAbove.of_resource rep2 (by
    intro address member; rw [owners2] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)
  -- A nonempty six-owner local can be dropped before ending its storage while
  -- the tuple still borrows the two old table cells.
  have positivePlan : RetirementPlan initial.roots [.drop 2, .storageDead 2] (initial.roots.set 2 none) :=
    RetirementPlan.of_presence (by decide +kernel)
  obtain ⟨cleanupWorld, cleanupActive, cleanupSteps, cleanupMachine, cleanupRoots, _, cleanupMemory⟩ :=
    positivePlan.complete_fresh (Helpers.callee 0 0) .done machine rfl
      (by intro slot member
          have same : slot = 13 := by simpa using member
          subst slot
          change 13 < 113
          decide)
      (by intro slot member
          have same : slot = 2 := by simpa using member
          subst slot
          change LocalOwnersAbove 2 entered initial 2
          exact fresh2)
      (by simp [retirementZeroChecks, clearBoxCount])
  have cleaned2 : cleanupActive.roots 2 = none := by rw [cleanupRoots]; simp [Roots.set]
  have retainedTuple : cleanupActive.state 13 = SourceEval.Evaluator.queryTuple .Empty .Empty :=
    (cleanupSteps.unshared_local_same_calls (by rw [initial_tuple]; intro value impossible; cases impossible) (by decide +kernel)).trans initial_tuple
  have cleanedMask : cleanupActive.state 2 = .empty := by
    obtain ⟨_, cleanupFrame⟩ := cleanupMachine.native.valid.2
    simpa only [cleaned2] using cleanupFrame.slots 2
  let callee := Helpers.callee 0 0
  obtain ⟨w1, a1, p1, m1, r1, c1, _, e1, v104, _⟩ := original_move_view_complete machine callee (prepCode 2)
    (source := 1) (destination := 104) (by decide) (by decide) rfl (table_typed memo) (.adt .table) (by change 104 < 113; decide) rfl
  have selected1 : a1.state 2 = Slot.ofValue (encodeResult answer) :=
    p1.closed_local_same (index := 2) machine.native.valid machine.native.callersValid machine.native.wellFormed
      (ofValue_typed (result_typed answer)) (.adt .embedding) rfl (by decide)
  obtain ⟨w2, a2, p2, m2, r2, c2, _, e2, v99, _⟩ := original_move_view_complete m1 callee (prepCode 4)
    (source := 2) (destination := 99) (by decide) (by decide) selected1 (result_typed answer) (.adt .embedding)
    (by rw [c1]; change 99 < 113; decide) (by simp [r1, Roots.set, initial, initialActivation, argumentRoots, packets])
  obtain ⟨w0, a0, p0, m0, r0, c0, _, empty0, raw0, _⟩ := original_open_local_complete m2 callee (SourceEval.Evaluator.finishCode 39)
    (slot := 0) (by decide) (by rw [c2, c1]; change 0 < 113; decide)
    (by simp [r2, r1, Roots.set, initial, initialActivation, argumentRoots])
  have prep : Calling.Prefix callee [] (SourceEval.Evaluator.finishCode 39) prepActions entered initial w0 a0 :=
    Calling.Prefix.append (suffix := SourceEval.Evaluator.finishCode 39) (rest := [.storageLive 0])
      (Calling.Prefix.append (suffix := prepCode 4) (rest := (prepActions.drop 2).take 2) p1 p2) p0
  have empty1 : a0.state 1 = .empty := by
    have tail : Calling.Prefix callee [] (SourceEval.Evaluator.finishCode 39) (prepActions.drop 2) w1 a1 w0 a0 :=
      Calling.Prefix.append (suffix := SourceEval.Evaluator.finishCode 39) (rest := [.storageLive 0]) p2 p0
    exact (tail.closed_local_same (index := 1) m1.native.valid m1.native.callersValid m1.native.wellFormed
      (by rw [e1]; exact .empty .u32) .u32 rfl (by decide)).trans e1
  have empty2 : a0.state 2 = .empty :=
    (p0.closed_local_same (index := 2) m2.native.valid m2.native.callersValid m2.native.wellFormed
      (by rw [e2]; exact .empty .u32) .u32 rfl (by decide)).trans e2
  have emptyFamily : ∀ slot ∈ [45, 44, 35, 34, 30, 29, 28, 27, 1, 2], a0.state slot = .empty := by
    intro slot member
    by_cases one : slot = 1
    · subst slot; exact empty1
    · by_cases two : slot = 2
      · subst slot; exact empty2
      · have high : 13 < slot := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
        exact (prep.closed_local_same (index := slot) machine.native.valid machine.native.callersValid machine.native.wellFormed
          (by rw [initial_high_empty slot high]; exact .empty .u32) .u32 rfl (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | contradiction | decide +kernel)).trans (initial_high_empty slot high)
  have parent : OriginalLoanMachine older [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] w0 a0 := by
    refine ⟨m0.native, m0.closed.enlarge (by simp), ?_, ?_⟩
    · intro slot member
      by_cases thirteen : slot = 13
      · subst slot; exact m0.zero 13 (by simp)
      · rw [emptyFamily slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)]; simp only [Slot.dropWork]
    · intro slot member
      by_cases thirteen : slot = 13
      · subst slot; exact m0.origins 13 (by simp)
      · exact LoanOrigin.of_closed m0.native.valid older.memory.length slot
          (by rw [emptyFamily slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)]; exact .empty .u32) .u32
  have held : ∀ slot ∈ [71, 85], LocalOwnersAbove older.memory.length w0 a0 slot := by
    intro slot member
    apply LocalOwnersAbove.of_zero
    have high : 13 < slot := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    have same := prep.closed_local_same (index := slot) machine.native.valid machine.native.callersValid machine.native.wellFormed
      (by rw [initial_high_empty slot high]; exact .empty .u32) .u32 rfl (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> decide +kernel)
    rw [same, initial_high_empty slot high]; simp only [Slot.dropWork]
  have transfer : OwnerTransfer 2 prepActions 99 :=
    .keep rfl (by decide) (.keep rfl (by decide) (.keep rfl (by decide)
      (.assign (fun _ _ _ fresh => OperandSourcesAbove.single_move fresh rfl) (.keep rfl (by decide) (.nil 99)))))
  have fresh99 := prep.owner_transfer transfer machine.native.valid machine.native.callersValid machine.native.wellFormed fresh2
  have selected0 : a0.state 99 = Slot.ofValue (encodeResult answer) :=
    (p0.closed_local_same (index := 99) m2.native.valid m2.native.callersValid m2.native.wellFormed
      (by rw [v99]; exact ofValue_typed (result_typed answer)) (.adt .embedding) rfl (by decide)).trans v99
  have table0 : a0.state 104 = Slot.ofValue (encodeTable memo) := by
    have tail : Calling.Prefix callee [] (SourceEval.Evaluator.finishCode 39) (prepActions.drop 2) w1 a1 w0 a0 :=
      Calling.Prefix.append (suffix := SourceEval.Evaluator.finishCode 39) (rest := [.storageLive 0]) p2 p0
    exact (tail.closed_local_same (index := 104) m1.native.valid m1.native.callersValid m1.native.wellFormed
      (by rw [v104]; exact ofValue_typed (table_typed memo)) (.adt .table) rfl (by decide)).trans v104
  have tuple0 : a0.state 13 = SourceEval.Evaluator.queryTuple .Empty .Empty :=
    (prep.unshared_local_same_calls (index := 13) (by rw [initial_tuple]; intro value eq; cases eq) (by decide +kernel)).trans initial_tuple
  obtain ⟨_, _, wp, ap, root110, root112, _, _, packed, mp, outputP, resultFresh, emptyP, bound110, dead111, bound112, _, _, rootsP, heldP, sameP, _⟩ :=
    SourceEval.Evaluator.pair_return_packing_complete (root0 := ⟨w2.memory.length, w2.memory.length⟩) parent callee answer memo selected0 table0 fresh99 held
      (by simp [r0, Roots.set]) raw0 empty0 (by rw [c0, c2, c1]; change 113 ≤ 113; rfl)
      (by intro slot member
          rw [r0, r2, r1]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> simp [Roots.set, initial, initialActivation, argumentRoots, packets])
  obtain ⟨b99, hb99⟩ := Activation.root_of_materialize parent.native.valid (value := encodeResult answer) (by rw [selected0]; exact Slot.materialize_ofValue _)
  obtain ⟨b104, hb104⟩ := Activation.root_of_materialize parent.native.valid (value := encodeTable memo) (by rw [table0]; exact Slot.materialize_ofValue _)
  obtain ⟨final, after, cleaned, finalMachine, output, fresh, retired, _, _, _, rootsAfter, _, sameAfter⟩ :=
    SourceEval.Evaluator.pair_return_retirement_complete mp callee answer memo outputP resultFresh
      (by intro slot member; exact emptyP slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact ⟨root112, bound112⟩
          · exact ⟨root110, bound110⟩
          · exact ⟨b104, by rw [rootsP 104 (by decide)]; exact hb104⟩
          · exact ⟨b99, by rw [rootsP 99 (by decide)]; exact hb99⟩) heldP
  obtain ⟨_, finalFrame⟩ := finalMachine.native.valid.2
  obtain ⟨r, _, represented⟩ := finalFrame.inspectSlot 0
  have boxes := represented.boxes
  rw [output] at boxes
  have eight : r.owners.length = 8 := boxes.trans (by with_unfolding_all rfl)
  have tupleP : ap.state 13 = SourceEval.Evaluator.queryTuple .Empty .Empty :=
    (sameP 13 (by decide) (by rw [tuple0]; intro value eq; cases eq)).trans tuple0
  refine ⟨w0, a0, final, after, r, finalMachine, output, fresh, represented, eight,
    (sameAfter 13 (by decide) (by rw [tupleP]; intro value eq; cases eq)).trans tupleP, ?_,
    Calling.Prefix.append (suffix := SourceEval.Evaluator.finishCode 56) (rest := (SourceEval.Evaluator.finishActions.drop 48).take 8) packed cleaned⟩
  intro slot member
  by_cases eleven : slot = 111
  · subst slot
    refine ⟨?_, by rw [rootsAfter 111 (by decide)]; exact dead111⟩
    exact (sameAfter 111 (by decide) (by rw [emptyP 111 (by decide)]; intro value eq; cases eq)).trans (emptyP 111 (by decide))
  · exact retired slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega)

-- Execute the same physical cleanup and observe all six descendant owners
-- retired, both old table owners still live, and the selected stack root gone.
example : (Calling.exec (Helpers.callee 0 0) []
    (.step (.drop 2) (.step (.storageDead 2) .done)) entered initial).map
      (fun result => match result.1 with
        | .next final after => ([2, 3, 4, 5, 6, 7].map final.live, final.live 0 && final.live 1, (after.roots 2).isSome)
        | .returned _ _ _ => ([], false, true)) =
    some ([false, false, false, false, false, false], true, false) := by
  decide +kernel

end SourceParentOutputTests
