module

import SubtreeProofs.Rust.SourceEvalCallingCertificate
import all SubtreeProofs.Rust.SourceHeapResources
import all SubtreeProofs.Rust.SourceHeapGraphTrace
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceCallingProgramTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed

private def empty : World := ⟨[], fun _ => none, fun _ => false⟩
private theorem empty_wf : empty.WellFormed := by simp [World.WellFormed, empty]
private def callerPackets : List ValueCell := [(.number 99, .number 99)]
private def base := empty.stackCells 77 (callerPackets.map Prod.fst)
private def caller := initialActivation empty 77 2 callerPackets
private def inputs : List ValueCell := [(.number 40, .number 40), (.number 2, .number 2)]
private def world := base.stackCells 10 (inputs.map Prod.fst)
private def active := initialActivation base 10 4 inputs
private theorem numeric_readable (w : World) (n : Nat) : Readable w.memory w.live (.number n) (.number n) :=
  ⟨[], .number n, by simp [AliveOn]⟩
private theorem inputs_readable : ∀ p ∈ inputs, Readable base.memory base.live p.1 p.2 := by
  intro p hp
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact numeric_readable _ _
private theorem base_wf : base.WellFormed := empty_wf.stackCells _ _
private theorem world_wf : world.WellFormed := base_wf.stackCells _ _
private theorem active_valid : active.Valid world := initialActivation_valid base_wf 10 4 inputs_readable (by decide +kernel)
private theorem caller_valid : caller.Valid world := by
  have hc : caller.Valid base := initialActivation_valid empty_wf 77 2 (by
    intro p hp
    have he : p = (.number 99, .number 99) := by simpa [callerPackets] using hp
    subst p; exact numeric_readable _ _) (by decide +kernel)
  obtain ⟨bound, used, hf⟩ := hc
  exact ⟨bound, used, hf.preserve (base.stackCells_keeps base_wf 10 (inputs.map Prod.fst) used).preserves⟩

private def openedWorld := world.allocate (.stack 10 0 3) (.node .tuple 0 [])
private def opened : Activation := { active with roots := active.roots.set 0 (some ⟨3, 3⟩), state := active.state.set 0 .empty }
private def callWorld := openedWorld.allocate (.stack 10 3 4) (.node .tuple 0 [])
private def callActive : Activation := { opened with roots := opened.roots.set 3 (some ⟨4, 4⟩), state := opened.state.set 3 .empty }
private def args : List SourceEval.Operand := [.move (.local 1), .move (.local 2)]
private def masks := (callActive.state.set 1 .empty).set 2 .empty
private def optionValue : Value := .node .optional 1 [.number 42]
private def afterWorld := callWorld.write 4 (.node .optional 1 [.number 42])
private def afterCall : Activation := { callActive with state := masks.set 3 (Slot.ofValue optionValue) }
private def good : SourceEval.Code := .step (.assign 0 (.use (.move (.field (.local 3) (some 1) 0)))) .ret
private def bad : SourceEval.Code := .step (.call .evaluate [] 0) .done
private def rest : SourceEval.Code := .switch (.discriminant (.local 3)) [(.variant .optional 1, 0)] (some 1)
  good bad (.step .undefinedBehavior .done)
private def program : SourceEval.Code := .step (.storageLive 0) (.step (.storageLive 3) (.step (.call .checkedAdd args 3) rest))
private def backend := Helpers.callee 8 16
private def domain : Derived.Ready := fun _ f packets => Helpers.Ready 8 f packets

private theorem first_step : Calling.instruction backend [caller] (world, active) (.storageLive 0) =
    some ((openedWorld, opened), SourceEval.Cost.local 1) := by with_unfolding_all rfl
private theorem second_step : Calling.instruction backend [caller] (openedWorld, opened) (.storageLive 3) =
    some ((callWorld, callActive), SourceEval.Cost.local 1) := by with_unfolding_all rfl
private theorem call_step : Calling.instruction backend [caller] (callWorld, callActive) (.call .checkedAdd args 3) =
    some ((afterWorld, afterCall), (SourceEval.Cost.local 3).plus (SourceEval.Cost.entry .checkedAdd)) := by with_unfolding_all rfl

private theorem ready_step {w next : World} {a after : Activation} {act : SourceEval.Action} {tail : SourceEval.Code} {cost : SourceEval.Cost}
    (hview : a.forgetRefs (.step act tail) = a)
    (hd : Calling.ReadyAt domain w a [caller] act)
    (hs : Calling.instruction backend [caller] (w, a) act = some ((next, after), cost))
    (hr : Calling.ReadyFor backend domain [caller] tail next after) :
    Calling.ReadyFor backend domain [caller] (.step act tail) w a := by
  change Calling.ReadyAt domain w (a.forgetRefs (.step act tail)) [caller] act ∧ _
  rw [hview]
  refine ⟨hd, ?_⟩
  intro middle current first he
  rw [hs] at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  exact hr

private theorem call_ready : Calling.ReadyAt domain callWorld callActive [caller] (.call .checkedAdd args 3) := by
  intro scanned suspended packets state hs hc he
  have current : callActive.scan callWorld = some (⟨[3, 1, 2, 4], [], []⟩ : Resources) := by with_unfolding_all rfl
  have callers : scanCallers callWorld [caller] = some (⟨[0], [], []⟩ : Resources) := by with_unfolding_all rfl
  rw [current] at hs
  cases hs
  rw [callers] at hc
  cases hc
  have actual : operands callWorld callActive.roots ([] ++ [0]) callActive.state args = some (inputs, masks) := by with_unfolding_all rfl
  rw [actual] at he
  cases he
  exact .checkedAdd 40 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem rest_ready : Calling.ReadyFor backend domain [caller] rest afterWorld afterCall := by
  intro key current hs
  have actual : Derived.scrutinee afterWorld afterCall [caller] (.discriminant (.local 3)) =
      some (.variant .optional 1, afterCall) := by with_unfolding_all rfl
  rw [actual] at hs
  cases hs
  constructor
  · intro index hi
    change some 0 = some index at hi
    cases hi
    exact ⟨fun _ => Calling.readyFor_noCalls backend domain [caller] good (by decide +kernel) _ _, by intro h; cases h⟩
  · intro middle resume first hb
    have returned : (Control.selectSource (.variant .optional 1) [(.variant .optional 1, 0)] (some 1)
        (fun _ => Calling.exec backend [caller] good afterWorld afterCall)
        (fun _ => Calling.exec backend [caller] bad afterWorld afterCall)).map
          (fun (flow, _) => match flow with | .returned _ _ _ => true | _ => false) = some true := by decide +kernel
    rw [hb] at returned
    cases returned

private theorem program_ready : Calling.ReadyFor backend domain [caller] program world active :=
  ready_step (by with_unfolding_all rfl) trivial first_step
    (ready_step (by with_unfolding_all rfl) trivial second_step
      (ready_step (by with_unfolding_all rfl) call_ready call_step rest_ready))

-- A call precedes routing, a payload moves out of the retained optional tag,
-- and early return skips an unsupported recursive call and a failing join.
example : (Calling.exec backend [caller] program world active).map (fun (flow, cost) =>
    (match flow with | .returned _ _ (_, .number n) => n | _ => 0, cost.work.steps,
      (flow.activation.state 1).materialize.isNone, (flow.activation.state 2).materialize.isNone,
      (flow.world.memory[0]?).map (fun c => match c with | .number n => n | _ => 0))) = some (42, 13, true, true, some 99) := by with_unfolding_all rfl

example : ∃ flow cost, Calling.exec backend [caller] program world active = some (flow, cost) ∧
    SourceEval.exec (SourceEval.run SourceEval.Certificate.original.body 8) program active.state = some (flow.snapshot, cost) ∧
    flow.Valid [caller] := by
  have hs : (Calling.exec backend [caller] program world active).isSome = true := by decide +kernel
  obtain ⟨⟨flow, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have h := Calling.exec_spec (Helpers.callee_respects 8 16) active_valid (by simpa using caller_valid) world_wf program program_ready hr
  exact ⟨flow, cost, hr, h.1, h.2.2.2⟩

-- The real post-argument activation and original caller reach the backend.
private def observing : Derived.Callees := fun w guards stack f packets =>
  match stack with
  | head :: suspended :: [] =>
    if head.frame = 10 ∧ suspended.frame = 77 ∧ (head.state 1).materialize.isNone ∧ (head.state 2).materialize.isNone then
      backend w guards stack f packets
    else none
  | _ => none
example : (Calling.exec observing [caller] program world active).isSome = true := by decide +kernel

-- Successful cleanup retires all four callee roots, preserves the caller root,
-- and preserves the same complete output packet and its source-derived value.
private def closed := do
  let (flow, cost) ← Calling.exec backend [caller] program world active
  match flow with
  | .next _ _ => none
  | .returned w a packet => some ((← close w a [caller] [] packet), packet, cost)
example : closed.map (fun (w, packet, cost) =>
    ((List.range 5).map w.live, (match packet.1 with | .number n => n | _ => 0), cost.work.steps)) =
    some ([true, false, false, false, false], 42, 13) := by with_unfolding_all rfl

-- Returning a reference into a scalar callee local is rejected at cleanup.
private def escapingWorld : World := ⟨[.number 7], fun a => if a = 0 then some (.stack 10 1 0) else none, fun a => decide (a = 0)⟩
private def escaping : Activation := ⟨10, 2, fun s => if s = 1 then some ⟨0, 0⟩ else none,
  fun s => if s = 1 then .number 7 else .empty⟩
example : close escapingWorld escaping [] [] (.shared ⟨0, []⟩, .reference (.number 7)) = none := by decide +kernel
example : close escapingWorld escaping [] [0] (.number 9, .number 9) = none := by decide +kernel

-- Remaining Box ownership cannot disappear during stack cleanup.
private def ownedWorld : World := ⟨[.number 7, .owned 0], fun a =>
  if a = 0 then some .box else if a = 1 then some (.stack 10 1 1) else none, fun a => decide (a < 2)⟩
private def owning : Activation := ⟨10, 2, fun s => if s = 1 then some ⟨1, 1⟩ else none,
  fun s => if s = 1 then .boxed (.number 7) else .empty⟩
example : close ownedWorld owning [] [] (.number 9, .number 9) = none := by decide +kernel

open verified_ordered_core
private def first (score : Aeneas.Std.U32) : CommonEmbedding := ⟨.Pair .Empty .Empty, score⟩
private def second (score : Aeneas.Std.U32) : CommonEmbedding := ⟨.Empty, score⟩
private def choiceBase : World := ⟨[.node .word 0 [], .node .word 0 []],
  fun a => if a < 2 then some .box else none, fun a => decide (a < 2)⟩
private def choicePackets (left right : Aeneas.Std.U32) : List ValueCell := [
  (.node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number left.val], encodeResult (first left)),
  (.node .embedding 0 [.node .word 0 [], .number right.val], encodeResult (second right))]
private def scoreOf (packet : ValueCell) : Nat :=
  match packet.1 with | .node .embedding 0 [_, .number n] => n | _ => 0

-- These consumers accept any checked parsed declaration with the actual choice
-- body/count. The type/provenance certificate remains an input, not a surrogate
-- hand-written declaration. Cleanup adds no Box events or source body steps.
example (decl : SourceEval.TypeReader.Definition) (hf : decl.source.function = .chooseLonger)
    (hcode : decl.source.code = SourceEval.Choice.body) (hn : decl.source.localCount = 6) :
    (Calling.invoke backend [] [] decl choiceBase (choicePackets 1#u32 3#u32)).map (fun (w, packet, cost) =>
      (scoreOf packet, (List.range 8).map w.live, cost.work.steps, cost.destroyed.boxes)) =
      some (3, [false, false, false, false, false, false, false, false], 34, 2) := by
  simp only [Calling.invoke, hf, hcode, hn]
  decide +kernel
example (decl : SourceEval.TypeReader.Definition) (hf : decl.source.function = .chooseLonger)
    (hcode : decl.source.code = SourceEval.Choice.body) (hn : decl.source.localCount = 6) :
    (Calling.invoke backend [] [] decl choiceBase (choicePackets 3#u32 3#u32)).map (fun (w, packet, cost) =>
      (scoreOf packet, (List.range 8).map w.live, traceResources w.memory packet.1 (Slot.ofValue packet.2), cost.work.steps)) =
      some (3, [true, true, false, false, false, false, false, false], some ⟨[0, 1], [0, 1], []⟩, 30) := by
  simp only [Calling.invoke, hf, hcode, hn]
  decide +kernel

example (decl : SourceEval.TypeReader.Definition) (hf : decl.source.function = .chooseLonger)
    (hcode : decl.source.code = SourceEval.Choice.body) (hn : decl.source.localCount = 6) :
    ∃ final packet cost, Calling.invoke backend [] [] decl choiceBase (choicePackets 1#u32 3#u32) = some (final, packet, cost) ∧
      packet.2 = encodeResult (OrderedSolver.selectResult (first 1#u32) (second 3#u32)) ∧
      cost = SourceEval.Choice.cost (first 1#u32) (second 3#u32) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed := by
  have hs : (Calling.invoke backend [] [] decl choiceBase (choicePackets 1#u32 3#u32)).isSome = true := by
    simp only [Calling.invoke, hf, hcode, hn]
    decide +kernel
  obtain ⟨⟨final, packet, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have hw : choiceBase.WellFormed := by simp [World.WellFormed, choiceBase]
  have hp : ∀ p ∈ choicePackets 1#u32 3#u32, Readable choiceBase.memory choiceBase.live p.1 p.2 := by
    intro p hm
    simp only [choicePackets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨[0, 1], .node (.cons (.node (.cons (.owned rfl (.node .nil))
        (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number _) .nil)), by simp [AliveOn, choiceBase]⟩
    · exact ⟨[], .node (.cons (.node .nil) (.cons (.number _) .nil)), by simp [AliveOn]⟩
  have h := SourceEval.Choice.invoking_refines 8 16 decl hf hcode hw (by simp) hp (first 1#u32) (second 3#u32) rfl hr
  exact ⟨final, packet, cost, hr, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

-- The checked source reader supplies this declaration, including its actual
-- six-local layout; execution does not need a user-provided declaration.
example : (Calling.invoke backend [] [] SourceEval.CallingCertificate.originalChoice choiceBase
    (choicePackets 1#u32 3#u32)).map (fun (w, packet, cost) =>
      (scoreOf packet, (List.range 8).map w.live, cost.work.steps)) =
      some (3, [false, false, false, false, false, false, false, false], 34) := by
  obtain ⟨hf, hn, hcode⟩ := SourceEval.CallingCertificate.originalChoice_spec
  simp only [Calling.invoke, hf, hn, hcode]
  decide +kernel

end SourceCallingProgramTests
