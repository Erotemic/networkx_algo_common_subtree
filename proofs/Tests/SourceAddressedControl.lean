import SubtreeProofs.Rust.SourceEvaluatorEntryPrefix
import SubtreeProofs.Rust.SourceChoiceCallTotality
import SubtreeProofs.Rust.SourceEvalAddressedChoice

namespace SourceAddressedControlTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed

private def base : World := ⟨[], fun _ => none, fun _ => false⟩
private def packets : List ValueCell := [(.node .optional 1 [.number 7], .node .optional 1 [.number 7])]
private def world := base.stackCells 10 (packets.map Prod.fst)
private def active := initialActivation base 10 4 packets
private theorem well_formed : base.WellFormed := by simp [World.WellFormed, base]
private theorem readable : ∀ p ∈ packets, Readable base.memory base.live p.1 p.2 := by
  intro p hp
  have he : p = (.node .optional 1 [.number 7], .node .optional 1 [.number 7]) := by simpa [packets] using hp
  subst p
  exact ⟨[], .node (.cons (.number 7) .nil), by simp [AliveOn]⟩
private theorem active_valid : active.Valid world := initialActivation_valid well_formed 10 4 readable (by decide +kernel)
private theorem world_valid : world.WellFormed := well_formed.stackCells _ _

private def program : SourceEval.Code :=
  .step (.storageLive 2) <|
  .step (.assign 2 (.use (.move (.field (.local 1) (some 1) 0)))) <|
  .switch (.discriminant (.local 1)) [(.variant .optional 1, 0)] (some 1)
    (.step (.storageLive 0) (.step (.assign 0 (.use (.copy (.local 2)))) .ret))
    (.step .undefinedBehavior .done) (.step .undefinedBehavior .done)

-- Moving the payload leaves a readable tag and a nonmaterializable aggregate.
-- The selected early return skips both the other branch and the continuation.
example : (Derived.exec [] program world active).map (fun (flow, cost) =>
    (match flow with | .returned _ _ (_, .number n) => n | _ => 0,
      (flow.activation.state 1).materialize.isNone, (flow.activation.state 0).materialize.isNone,
      cost.work.steps, cost.destroyed.visits)) = some (7, true, true, 11, 0) := by decide +kernel

example : ∃ flow cost, Derived.exec [] program world active = some (flow, cost) ∧
    (∀ call, SourceEval.exec call program active.state = some (flow.snapshot, cost)) ∧ flow.Valid [] := by
  have hs : (Derived.exec [] program world active).isSome = true := by decide +kernel
  obtain ⟨⟨flow, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have h := Derived.exec_spec (fun _ _ => none) active_valid (by simp) world_valid program hr
  exact ⟨flow, cost, hr, fun call => (Derived.exec_spec call active_valid (by simp) world_valid program hr).1, h.2.2.2⟩

example : discriminant (world.retire [0]) active.roots active.state (.local 1) = none := by decide +kernel
example : (Derived.exec [] (.switch (.value (.boolean false)) [] none .done .done .done) world active).isNone = true := by decide +kernel
example : (Derived.exec [] (.switch (.value (.boolean true)) [(.boolean true, 2)] none .done .done .done) world active).isNone = true := by decide +kernel

-- Physical return extraction checks caller loans into local zero. It cannot
-- transfer a scalar still referenced by a suspended caller, despite zero Boxes.
private def borrowedWorld : World := ⟨[.number 7, .shared ⟨0, []⟩], fun a =>
  if a = 0 then some (.stack 10 0 0) else if a = 1 then some (.stack 20 1 1) else none,
  fun a => decide (a < 2)⟩
private def returnActive : Activation := ⟨10, 1, fun slot => if slot = 0 then some ⟨0, 0⟩ else none,
  fun slot => if slot = 0 then .number 7 else .empty⟩
private def returnCaller : Activation := ⟨20, 2, fun slot => if slot = 1 then some ⟨1, 1⟩ else none,
  fun slot => if slot = 1 then .shared (.number 7) else .empty⟩
example : (Derived.returnValue [returnCaller] borrowedWorld returnActive).isNone = true := by decide +kernel
example : (Derived.returnValue [] borrowedWorld returnActive).isSome = true := by decide +kernel

-- The complete actual choice body has both boolean winner branches, a join,
-- losing-value destruction and return extraction. The first input owns Boxes
-- zero and one; the second is inline and owns none.
open verified_ordered_core
private def first (score : Aeneas.Std.U32) : CommonEmbedding := ⟨.Pair .Empty .Empty, score⟩
private def second (score : Aeneas.Std.U32) : CommonEmbedding := ⟨.Empty, score⟩
private def choiceBase : World := ⟨[.node .word 0 [], .node .word 0 []],
  fun a => if a < 2 then some .box else none, fun a => decide (a < 2)⟩
private def choicePackets (left right : Aeneas.Std.U32) : List ValueCell := [
  (.node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number left.val], encodeResult (first left)),
  (.node .embedding 0 [.node .word 0 [], .number right.val], encodeResult (second right))]
private def choiceWorld (left right : Aeneas.Std.U32) := choiceBase.stackCells 30 ((choicePackets left right).map Prod.fst)
private def choiceActive (left right : Aeneas.Std.U32) := initialActivation choiceBase 30 6 (choicePackets left right)
private def choiceRun (left right : Aeneas.Std.U32) :=
  Derived.exec [] SourceEval.Choice.body (choiceWorld left right) (choiceActive left right)

private theorem choice_well_formed : choiceBase.WellFormed := by simp [World.WellFormed, choiceBase]
private theorem choice_readable (left right : Aeneas.Std.U32) :
    ∀ p ∈ choicePackets left right, Readable choiceBase.memory choiceBase.live p.1 p.2 := by
  intro p hp
  simp only [choicePackets, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨[0, 1], .node (.cons (.node (.cons (.owned rfl (.node .nil))
      (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number left.val) .nil)), by simp [AliveOn, choiceBase]⟩
  · exact ⟨[], .node (.cons (.node .nil) (.cons (.number right.val) .nil)), by simp [AliveOn]⟩

private def outputResources (flow : Derived.Flow) : Option Resources :=
  match flow with
  | .returned world _ (cell, value) => traceResources world.memory cell (Slot.ofValue value)
  | _ => none
private def outputScore (flow : Derived.Flow) : Nat :=
  match flow with
  | .returned _ _ (_, .node .embedding 0 [_, .number n]) => n
  | _ => 0

-- Selecting the second input retires both losing Boxes, with their exact visits.
example : (choiceRun 1#u32 3#u32).map (fun (flow, cost) =>
    (outputScore flow, [flow.world.live 0, flow.world.live 1], outputResources flow,
      cost.work.steps, cost.destroyed.visits, cost.destroyed.boxes)) =
    some (3, [false, false], some ⟨[], [], []⟩, 33, 7, 2) := by decide +kernel

-- Selecting the first input retains the same concrete owner identities. Ties
-- select that same input, matching the already proved native choice rule.
example : (choiceRun 5#u32 3#u32).map (fun (flow, cost) =>
    (outputScore flow, [flow.world.live 0, flow.world.live 1], outputResources flow,
      cost.work.steps, cost.destroyed.visits, cost.destroyed.boxes)) =
    some (5, [true, true], some ⟨[0, 1], [0, 1], []⟩, 29, 3, 0) := by decide +kernel
example : (choiceRun 3#u32 3#u32).map (fun (flow, _) => outputResources flow) =
    some (some ⟨[0, 1], [0, 1], []⟩) := by decide +kernel

-- Lift a complete physical execution to the actual pinned source body and
-- independent native result, without rebuilding the old choice proof.
example : ∃ final after cell work,
    Derived.exec [] (SourceEval.Certificate.original.body .chooseLonger) (choiceWorld 1#u32 3#u32) (choiceActive 1#u32 3#u32) =
      some (.returned final after (cell, encodeResult (OrderedSolver.selectResult (first 1#u32) (second 3#u32))), work) ∧
    Readable final.memory final.live cell (encodeResult (OrderedSolver.selectResult (first 1#u32) (second 3#u32))) ∧ after.Valid final := by
  have hs : (choiceRun 1#u32 3#u32).isSome = true := by decide +kernel
  obtain ⟨⟨flow, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have hactual : Derived.exec [] (SourceEval.Certificate.original.body .chooseLonger) (choiceWorld 1#u32 3#u32) (choiceActive 1#u32 3#u32) = some (flow, cost) := by
    simpa only [SourceEval.Choice.actual_body, choiceRun] using hr
  have hv := initialActivation_valid choice_well_formed 30 6 (choice_readable 1#u32 3#u32) (by decide +kernel)
  obtain ⟨final, after, cell, he, _, hp, ha, _, _, _, _⟩ :=
    SourceEval.Choice.addressed_refines hv (by simp) (choice_well_formed.stackCells _ _) (first 1#u32) (second 3#u32) rfl hactual
  exact ⟨final, after, cell, cost, he ▸ hactual, hp, ha⟩

-- Retained tags inspect the partial mask after a constructed source field move.
private def afterPayload : Activation := {active with state := active.state.set 1 (.node .optional 1 [.empty])}
private theorem payload_source : active.state.move (.field (.local 1) (some 1) 0) =
    some (.number 7, afterPayload.state) := by with_unfolding_all rfl
private theorem after_payload_valid : afterPayload.Valid world := by
  obtain ⟨_, frame⟩ := active_valid.2
  exact ⟨active_valid.1, _, frame.move payload_source⟩
example : Derived.scrutinee world afterPayload [] (.discriminant (.local 1)) =
    some (.variant .optional 1, afterPayload) := by
  exact Derived.scrutinee_complete after_payload_valid (by simp) (.discriminant (.local 1))
    (by with_unfolding_all rfl) (by intros; trivial)

-- Fresh return storage has no older caller reads. Return extraction and full
-- checked cleanup are both constructed, rather than assumed successful.
private def freshReturnWorld := base.allocate (.stack 10 0 0) (.number 7)
private def freshReturn : Activation := ⟨10, 1, fun slot => if slot = 0 then some ⟨0, 0⟩ else none,
  fun slot => if slot = 0 then .number 7 else .empty⟩
private theorem fresh_return_valid : freshReturn.Valid freshReturnWorld := by
  refine ⟨?_, [0], ?_, ?_⟩
  · intro slot hs
    change 1 ≤ slot at hs
    simp [freshReturn, show slot ≠ 0 by omega]
  · intro a ha
    have zero : a = 0 := by simpa using ha
    subst a
    rfl
  · intro slot
    by_cases zero : slot = 0
    · subst slot
      exact ⟨_, [], rfl, rfl, .number 7, by simp⟩
    · simp [freshReturn, zero]
private theorem fresh_frame : OwnerFrame freshReturnWorld (freshReturn.owners freshReturnWorld ++ (callerOwners freshReturnWorld [] ++ [])) := by
  rw [show freshReturn.owners freshReturnWorld ++ (callerOwners freshReturnWorld [] ++ []) = [] by decide +kernel]
  exact ⟨by simp, by simp [BoxOwners], by simp [AliveOn]⟩
private theorem fresh_coverage : BoxCoverage freshReturnWorld (freshReturn.owners freshReturnWorld ++ (callerOwners freshReturnWorld [] ++ [])) := by
  intro a classified _
  by_cases zero : a = 0 <;> simp [freshReturnWorld, World.allocate, base, zero] at classified
private theorem fresh_loan : Derived.ReturnLoansAllowed freshReturnWorld freshReturn [] ⟨0, 0⟩ := by
  apply Derived.ReturnLoansAllowed.of_closed_preserved (binding := ⟨0, 0⟩) (previous := {})
    (before := base) (callerView := .nil) (hw := well_formed)
    (kept := (base.allocate_keeps well_formed (.stack 10 0 0) (.number 7) []).preserves) (fresh := by decide +kernel)
  intro slot bound
  have zero : slot = 0 := by change slot < 1 at bound; omega
  subst slot
  with_unfolding_all exact ⟨.u32, .number (value := 7) (by decide +kernel), .u32⟩

example : ∃ cell owners final, Derived.returnValue [] freshReturnWorld freshReturn =
      some (.returned freshReturnWorld {freshReturn with state := freshReturn.state.set 0 .empty} (cell, .number 7), SourceEval.Cost.local 1) ∧
    close freshReturnWorld {freshReturn with state := freshReturn.state.set 0 .empty} [] [] (cell, .number 7) = some final ∧
    final.live 0 = false ∧ Readable final.memory final.live cell (.number 7) ∧
    Footprint final.memory cell owners ∧ OwnerFrame final (owners ++ (callerOwners final [] ++ [])) ∧
    BoxCoverage final (owners ++ (callerOwners final [] ++ [])) := by
  have separate : freshReturn.RootsSeparate [] := by intros _ _ _ current hm; cases hm
  obtain ⟨cell, owners, run, _, valid, readable, footprint, frame, coverage⟩ := Derived.returnValue_total (binding := ⟨0, 0⟩) (value := .number 7)
    fresh_return_valid (by simp) (well_formed.allocate _ _) separate fresh_frame fresh_coverage
    (by rfl) (by with_unfolding_all rfl) fresh_loan
  have zero : ∀ slot, ((freshReturn.state.set 0 .empty) slot).dropWork.boxes = 0 := by
    intro slot
    by_cases same : slot = 0 <;> simp [Partial.Locals.set, freshReturn, same, Slot.dropWork]
  obtain ⟨final, closed, _, _, _, output, _, retired, foot, frame, coverage⟩ := close_total (packet := (cell, .number 7)) (owners := owners) (guards := []) (external := []) valid (by simp)
    (well_formed.allocate _ _) separate zero readable (.number (value := 7) (by decide +kernel)) .u32 footprint frame coverage
    (by intro current represented; exact List.nil_subset _)
    (by intro slot binding root current represented; cases represented; simp)
  exact ⟨cell, owners, final, run, closed, retired 0 ⟨0, 0⟩ (by rfl), output, foot, frame, coverage⟩

private theorem choice_resources (left right : Aeneas.Std.U32) :
    FieldsFootprint choiceBase.memory ((choicePackets left right).map Prod.fst) [0, 1] ∧
    OwnerFrame choiceBase ([0, 1] ++ (callerOwners choiceBase [] ++ [])) ∧
    BoxCoverage choiceBase ([0, 1] ++ (callerOwners choiceBase [] ++ [])) := by
  have input : FieldsFootprint choiceBase.memory ((choicePackets left right).map Prod.fst) [0, 1] :=
    .cons (.node (.cons (.node (.cons (.owned rfl (.node .nil))
      (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number left.val) .nil)))
      (.cons (.node (.cons (.node .nil) (.cons (.number right.val) .nil))) .nil)
  have frame : OwnerFrame choiceBase ([0, 1] ++ (callerOwners choiceBase [] ++ [])) := by
    refine ⟨by decide +kernel, ?_, ?_⟩
    · intro address member
      have cases : address = 0 ∨ address = 1 := by simpa [callerOwners] using member
      rcases cases with rfl | rfl <;> rfl
    · intro address member
      have cases : address = 0 ∨ address = 1 := by simpa [callerOwners] using member
      rcases cases with rfl | rfl <;> rfl
  have covered : BoxCoverage choiceBase ([0, 1] ++ (callerOwners choiceBase [] ++ [])) := by
    intro address classified _
    by_cases small : address < 2
    · have cases : address = 0 ∨ address = 1 := by omega
      simpa [callerOwners] using cases
    · have bound : address < 2 := by simpa [choiceBase] using classified
      exact False.elim (small bound)
  exact ⟨input, frame, covered⟩

-- Arbitrary score pairs and arbitrary helper budgets now have a constructed
-- parsed entry/body/closure run. The owned nonempty first word exercises both
-- losing Box retirement and tie retention; no run-success fact is supplied.
example (left right : Aeneas.Std.U32) (fuel budget : Nat) :
    ∃ final packet,
      Calling.guardedInvoke (Helpers.callee fuel budget) [] [] SourceEval.CallingCertificate.originalChoice
        choiceBase (choicePackets left right) = some (final, packet, SourceEval.Choice.cost (first left) (second right)) ∧
      packet.2 = encodeResult (OrderedSolver.selectResult (first left) (second right)) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      ∃ owners, Footprint final.memory packet.1 owners ∧
        OwnerFrame final owners ∧ BoxCoverage final owners := by
  have firstReadable := choice_readable left right
    (.node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number left.val], encodeResult (first left))
    (by simp [choicePackets])
  have secondReadable := choice_readable left right
    (.node .embedding 0 [.node .word 0 [], .number right.val], encodeResult (second right))
    (by simp [choicePackets])
  obtain ⟨input, frame, covered⟩ := choice_resources left right
  obtain ⟨final, packet, run, result, readable, wf, _, owners, foot, frame, coverage⟩ :=
    SourceEval.Choice.invoke_total fuel budget (guards := []) (inputOwners := [0, 1]) (external := []) choice_well_formed (by simp) (first left) (second right)
      (.node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number left.val])
      (.node .embedding 0 [.node .word 0 [], .number right.val])
      firstReadable secondReadable (previous := {}) .nil input frame covered (by simp) (by simp)
  exact ⟨final, packet, run, result, readable, wf, owners, foot,
    by simpa only [callerOwners, List.flatMap_nil, List.nil_append, List.append_nil] using frame,
    by simpa only [callerOwners, List.flatMap_nil, List.nil_append, List.append_nil] using coverage⟩

-- A parent activation moves both owned arguments into actual recursive choice,
-- then receives its native result in a freshly allocated destination. Fuel one
-- suffices for the callee, and all score pairs retain the exact full call cost.
example (left right : Aeneas.Std.U32) (budget fuel : Nat) :
    let before := choiceWorld left right
    let parent := choiceActive left right
    let openedWorld := before.allocate (.stack parent.frame 3 before.memory.length) (.node .tuple 0 [])
    let opened : Activation := {parent with roots := parent.roots.set 3 (some ⟨before.memory.length, before.memory.length⟩), state := parent.state.set 3 .empty}
    ∃ final after,
      Derived.call (Recursive.original budget (fuel + 1)) openedWorld opened [] .chooseLonger
        [.move (.local 1), .move (.local 2)] 3 = some (final, after,
          (SourceEval.Cost.local 3).plus (SourceEval.Choice.cost (first left) (second right))) ∧
      after.state 3 = Slot.ofValue (encodeResult (OrderedSolver.selectResult (first left) (second right))) ∧
      after.Valid final ∧ final.WellFormed ∧
      OwnerFrame final (after.owners final) ∧ BoxCoverage final (after.owners final) := by
  dsimp only
  let before := choiceWorld left right
  let parent := choiceActive left right
  let openedWorld := before.allocate (.stack parent.frame 3 before.memory.length) (.node .tuple 0 [])
  let opened : Activation := {parent with roots := parent.roots.set 3 (some ⟨before.memory.length, before.memory.length⟩), state := parent.state.set 3 .empty}
  have valid : parent.Valid before := initialActivation_valid choice_well_formed 30 6 (choice_readable left right) (by simp [choicePackets])
  have wf : before.WellFormed := choice_well_formed.stackCells _ _
  obtain ⟨input, inputFrame, inputCoverage⟩ := choice_resources left right
  have entry := (enter_complete choice_well_formed 30 6 (choice_readable left right) (by simp [choicePackets])).1
  have initialResources := enter_owner_resources choice_well_formed 30 6 (callers := []) (by simp)
    (choice_readable left right) input inputFrame inputCoverage entry
  have liveRun := Derived.storageLive_complete valid (callers := []) (by simp) (slot := 3) (by change 3 < 6; decide +kernel) (by rfl)
  have liveSpec := Derived.storageLive_spec valid (by simp) wf liveRun
  have liveResources := Derived.storageLive_owner_resources valid (by simp) wf initialResources.1 initialResources.2 liveRun
  have openedValid : opened.Valid openedWorld := liveSpec.valid
  have openedWf : openedWorld.WellFormed := liveSpec.wellFormed
  let masks := (opened.state.set 1 .empty).set 2 .empty
  have allEmpty : ∀ slot, masks slot = .empty := by
    intro slot
    by_cases one : slot = 1
    · subst slot; simp [masks, Partial.Locals.set]
    · by_cases two : slot = 2
      · subst slot; simp [masks, Partial.Locals.set]
      · by_cases three : slot = 3
        · subst slot; simp [masks, opened, Partial.Locals.set]
        · simp only [masks, opened, parent, choiceActive, initialActivation, choicePackets, List.map_cons,
            List.map_nil, Partial.Locals.set, one, two, three, ite_false]
          exact SourceEval.Choice.initial_empty (first left) (second right) one two
  have maskTyped : ∀ slot, ∃ ty, SlotTyped (masks slot) ty ∧ Borrow.Closed ty := by
    intro slot
    exact ⟨.u32, by rw [allEmpty slot]; exact .empty _, .u32⟩
  have source : SourceEval.operands opened.state [.move (.local 1), .move (.local 2)] =
      some ([encodeResult (first left), encodeResult (second right)], masks) := by
    simp [opened, parent, choiceActive, initialActivation, choicePackets, SourceEval.initialState, Partial.Locals.lift, initialEnv,
      SourceEval.operands, SourceEval.operand, Partial.Locals.move, splitPlace, Slot.take,
      Slot.materialize_ofValue, Partial.Locals.set, masks]
  have closed : ClosedState opened.state := by
    exact (SourceEval.Choice.initial_closed (first left) (second right)).clear 3
  have moves : ∀ current suspended, Scanned openedWorld opened current → Callers openedWorld [] suspended →
      ∀ op ∈ ([.move (.local 1), .move (.local 2)] : List SourceEval.Operand),
        Allowed openedWorld opened.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scan callers op member
    cases callers
    have noLoans := scan.inventory.closed_loans (fun slot _ => closed slot)
    rw [noLoans]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> intro cell pointer located forbidden <;> cases forbidden
  have loans : Derived.RootLoansAllowed openedWorld {opened with state := masks} [] 3 ⟨before.memory.length, before.memory.length⟩ := by
    intro remainder suspended remaining callers forbidden
    cases callers
    have noLoans := remaining.closed_loans (fun slot _ => maskTyped slot)
    simp only [noLoans, List.nil_append, List.not_mem_nil] at forbidden
  have transfer : Derived.ArgumentsLoansAllowed openedWorld opened [] [.move (.local 1), .move (.local 2)] masks := by
    intro guarded packets owners suspended arguments footprint callers
    have noLoans := callers.closed_loans (by
      intro current member slot _
      have same : current = {opened with state := masks} := by simpa only [List.mem_singleton] using member
      subst current
      exact maskTyped slot)
    rw [noLoans]
    exact List.disjoint_nil_right _
  obtain ⟨final, after, run, state, _, valid, wf, _, frame, coverage⟩ := Derived.choice_call_total budget fuel
    (slot := 3) (binding := ⟨before.memory.length, before.memory.length⟩) (masks := masks)
    openedValid (by simp) openedWf (by intro _ _ _ current member; cases member)
    liveResources.2.2.1 liveResources.2.2.2 [.move (.local 1), .move (.local 2)]
    (by simp [opened, Roots.set]) (first left) (second right) source (allEmpty 3) moves loans transfer
  refine ⟨final, after, run, ?_, valid, wf, ?_, ?_⟩
  · rw [state]; simp only [Partial.Locals.set, ite_true]
  · simpa only [callerOwners, List.flatMap_nil, List.nil_append, List.append_nil] using frame
  · simpa only [callerOwners, List.flatMap_nil, List.nil_append, List.append_nil] using coverage

-- Both query pointers refer inside a Box owned by the input table. Construct
-- the actual entry/common prefix without an owner-versus-query-loan ban.
private def aliasTable : MemoTable := .Entry ⟨.Empty, .Empty, ⟨.Empty, 0#u32⟩⟩ .Empty
private def aliasEntry : Cell := .node .entry 0
  [.node .word 0 [], .node .word 0 [], .node .embedding 0 [.node .word 0 [], .number 0]]
private def aliasWorld : World := ⟨[aliasEntry, .node .table 0 []],
  fun a => if a < 2 then some .box else none, fun a => decide (a < 2)⟩
private def aliasTableCell : Cell := .node .table 1 [.owned 0, .owned 1]
private def aliasPackets : List ValueCell := SourceEval.Evaluator.inputPackets
  (.shared ⟨0, [0]⟩) (.shared ⟨0, [1]⟩) aliasTableCell .Empty .Empty aliasTable

private theorem alias_entry_graph : Graph aliasWorld.memory aliasEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult ⟨.Empty, 0#u32⟩]) [] := by
  have result : Graph aliasWorld.memory (.node .embedding 0 [.node .word 0 [], .number 0])
      (encodeResult ⟨.Empty, 0#u32⟩) [] := .node (.cons (.node .nil) (.cons (.number 0) .nil))
  exact .node (.cons (.node .nil) (.cons (.node .nil) (.cons result .nil)))

private theorem alias_entry_footprint : Footprint aliasWorld.memory aliasEntry [] := by
  have result : Footprint aliasWorld.memory (.node .embedding 0 [.node .word 0 [], .number 0]) [] :=
    .node (.cons (.node .nil) (.cons (.number 0) .nil))
  exact .node (.cons (.node .nil) (.cons (.node .nil) (.cons result .nil)))

private theorem alias_readable : ∀ p ∈ aliasPackets, Readable aliasWorld.memory aliasWorld.live p.1 p.2 := by
  intro p member
  simp only [aliasPackets, SourceEval.Evaluator.inputPackets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨[0], .shared rfl (.node .nil), by simp [AliveOn, aliasWorld]⟩
  · exact ⟨[0], .shared rfl (.node .nil), by simp [AliveOn, aliasWorld]⟩
  · exact ⟨[0, 1], .node (.cons (.owned rfl alias_entry_graph)
      (.cons (.owned rfl (.node .nil)) .nil)), by simp [AliveOn, aliasWorld]⟩

private theorem alias_resources : FieldsFootprint aliasWorld.memory (aliasPackets.map Prod.fst) [0, 1] ∧
    OwnerFrame aliasWorld ([0, 1] ++ (callerOwners aliasWorld [] ++ [])) ∧
    BoxCoverage aliasWorld ([0, 1] ++ (callerOwners aliasWorld [] ++ [])) := by
  refine ⟨?_, ?_, ?_⟩
  · have table : Footprint aliasWorld.memory aliasTableCell [0, 1] :=
      .node (.cons (.owned rfl alias_entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))
    exact .cons (.shared _) (.cons (.shared _) (.cons table .nil))
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · intro address member
      have cases : address = 0 ∨ address = 1 := by simpa [callerOwners] using member
      rcases cases with rfl | rfl <;> rfl
    · intro address member
      have cases : address = 0 ∨ address = 1 := by simpa [callerOwners] using member
      rcases cases with rfl | rfl <;> rfl
  · intro address classified _
    have bound : address < 2 := by simpa [aliasWorld] using classified
    have cases : address = 0 ∨ address = 1 := by omega
    simpa [callerOwners] using cases

example : ∃ entered active minimumFuel minimumBudget final after,
    enter aliasWorld aliasWorld.memory.length SourceEval.CallingCertificate.originalEvaluator.source.localCount aliasPackets =
      some (entered, active) ∧
    LoanSafeMachine aliasWorld [] {} [] final after ∧
    ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.afterLookup
        (SourceEval.Evaluator.borrowPrefix ++ [.call .lookup SourceEval.Evaluator.lookupArgs 4]) entered active final after := by
  have resources := alias_resources
  obtain ⟨entered, active, minFuel, minBudget, final, after, entryRun, _, _, _, _, _, machine, stable⟩ :=
    SourceEval.Evaluator.entry_lookup_complete (by simp [World.WellFormed, aliasWorld])
      (by simp) Callers.nil .Empty .Empty aliasTable (.shared ⟨0, [0]⟩) (.shared ⟨0, [1]⟩) aliasTableCell
      (alias_readable (.shared ⟨0, [0]⟩, .reference (encodeWord .Empty)) (by simp [aliasPackets, SourceEval.Evaluator.inputPackets]))
      (alias_readable (.shared ⟨0, [1]⟩, .reference (encodeWord .Empty)) (by simp [aliasPackets, SourceEval.Evaluator.inputPackets]))
      (alias_readable (aliasTableCell, encodeTable aliasTable) (by simp [aliasPackets, SourceEval.Evaluator.inputPackets])) resources.1 resources.2.1 resources.2.2
  exact ⟨entered, active, minFuel, minBudget, final, after, entryRun, machine, stable⟩

-- The structural rule intentionally excludes unit and reference-containing
-- referents; general loan guards still handle those separate cases.
example : ¬ NativeData (.node .tuple 0 []) := by
  intro data
  cases data with
  | node nonempty _ => exact nonempty rfl rfl rfl

example : ¬ NativeData (.reference (encodeWord .Empty)) := by intro data; cases data

end SourceAddressedControlTests
