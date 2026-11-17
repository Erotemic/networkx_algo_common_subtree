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

end SourceAddressedControlTests
