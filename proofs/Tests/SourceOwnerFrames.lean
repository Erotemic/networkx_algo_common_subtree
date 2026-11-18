module

import SubtreeProofs.Rust.SourceOwnerCallTransfer
import SubtreeProofs.Rust.SourceEvalTypedRecursive
import SubtreeProofs.Rust.SourceEvalHelperCalls
import all SubtreeProofs.Rust.SourceHeapResources
import all SubtreeProofs.Rust.SourceHeapGraphTrace
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceOwnerFramesTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval SourceEval.Addressed

private def world : World := ⟨[.number 7, .owned 0, .node .tuple 0 [.owned 1, .owned 3],
  .number 9, .node .tuple 0 [], .shared ⟨3, []⟩, .owned 7, .number 42, .shared ⟨3, []⟩],
  fun a => if a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 7 then some .box
    else if a = 2 then some (.stack 10 1 2) else if a = 4 then some (.stack 10 0 4)
    else if a = 5 then some (.stack 10 2 5) else if a = 6 then some (.stack 20 0 6)
    else if a = 8 then some (.stack 20 1 8) else none,
  fun a => decide (a < 9)⟩
private def whole : Slot := .node .tuple 0 [.boxed (.boxed (.number 7)), .boxed (.number 9)]
private def rest : Slot := .node .tuple 0 [.boxed .empty, .boxed (.number 9)]
private def active : Activation := ⟨10, 3, fun s =>
  if s = 0 then some ⟨4, 4⟩ else if s = 1 then some ⟨2, 2⟩ else if s = 2 then some ⟨5, 5⟩ else none,
  fun s => if s = 1 then whole else if s = 2 then .shared (.number 9) else .empty⟩
private def caller : Activation := ⟨20, 2, fun s =>
  if s = 0 then some ⟨6, 6⟩ else if s = 1 then some ⟨8, 8⟩ else none,
  fun s => if s = 0 then .boxed (.number 42) else if s = 1 then .shared (.number 9) else .empty⟩
private def payload : Place := .deref (.field (.local 1) none 0)
private def afterMove : Activation := { active with state := active.state.set 1 rest }
private def moved : ValueCell := (.owned 0, .boxed (.number 7))

private theorem active_valid : active.Valid world := by
  refine ⟨?_, List.range 9, ?_, ?_⟩
  · intro slot hs
    change 3 ≤ slot at hs
    simp [active, show slot ≠ 0 by omega, show slot ≠ 1 by omega, show slot ≠ 2 by omega]
  · intro a ha
    exact of_decide_eq_true (by simpa using ha : decide (a < 9) = true)
  · intro slot
    by_cases h0 : slot = 0
    · subst slot
      exact ⟨_, [], rfl, rfl, .empty _, by simp⟩
    · by_cases h1 : slot = 1
      · subst slot
        exact ⟨_, [0, 1, 3], rfl, rfl,
          .node (.cons (.owned rfl (.owned rfl (.number 7))) (.cons (.owned rfl (.number 9)) .nil)), by simp⟩
      · by_cases h2 : slot = 2
        · subst slot
          exact ⟨_, [3], rfl, rfl, .shared (.shared rfl (.number 9)), by simp⟩
        · simp [active, h0, h1, h2]
private theorem caller_valid : caller.Valid world := by
  refine ⟨?_, List.range 9, ?_, ?_⟩
  · intro slot hs
    change 2 ≤ slot at hs
    simp [caller, show slot ≠ 0 by omega, show slot ≠ 1 by omega]
  · intro a ha
    exact of_decide_eq_true (by simpa using ha : decide (a < 9) = true)
  · intro slot
    by_cases h0 : slot = 0
    · subst slot
      exact ⟨_, [7], rfl, rfl, .owned rfl (.number 42), by simp⟩
    · by_cases h1 : slot = 1
      · subst slot
        exact ⟨_, [3], rfl, rfl, .shared (.shared rfl (.number 9)), by simp⟩
      · simp [caller, h0, h1]
private theorem well_formed : world.WellFormed := by
  constructor
  · intro a
    change ((if a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 7 then some Class.box
      else if a = 2 then some (.stack 10 1 2) else if a = 4 then some (.stack 10 0 4)
      else if a = 5 then some (.stack 10 2 5) else if a = 6 then some (.stack 20 0 6)
      else if a = 8 then some (.stack 20 1 8) else none).isSome = true ↔ a < 9)
    split_ifs <;> simp_all <;> omega
  · intro a ha
    exact of_decide_eq_true ha
private theorem owner_frame : OwnerFrame world (active.owners world ++ (callerOwners world [caller] ++ [])) := by
  rw [show active.owners world ++ (callerOwners world [caller] ++ []) = [0, 1, 3, 7] by decide +kernel]
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> rfl
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> rfl
private theorem coverage : BoxCoverage world (active.owners world ++ (callerOwners world [caller] ++ [])) := by
  rw [show active.owners world ++ (callerOwners world [caller] ++ []) = [0, 1, 3, 7] by decide +kernel]
  intro a hc _
  change (if a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 7 then some Class.box else _) = some .box at hc
  split_ifs at hc with h <;> simp_all

-- Moving the inner Box retains the enclosing Box shell and the sibling owner.
private theorem move_step : operand world active.roots [3] active.state (.move payload) = some (moved, afterMove.state) := by
  with_unfolding_all rfl
example : active.owners world = [0, 1, 3] ∧ afterMove.owners world = [1, 3] := by decide +kernel
example : ∃ owners, Footprint world.memory moved.1 owners ∧
    OwnerFrame world (owners ++ (afterMove.owners world ++ (callerOwners world [caller] ++ []))) :=
  operand_owner_frame active_valid owner_frame move_step

private def args : List SourceEval.Operand := [.move payload, .copy (.local 2), .copy (.local 2), .move (.field (.local 1) none 1)]
private def packets : List ValueCell := [moved, (.shared ⟨3, []⟩, .reference (.number 9)),
  (.shared ⟨3, []⟩, .reference (.number 9)), (.owned 3, .boxed (.number 9))]
private def afterArgs : Activation := { active with state := afterMove.state.set 1 (.node .tuple 0 [.boxed .empty, .empty]) }
private theorem args_step : operands world active.roots [3] active.state args = some (packets, afterArgs.state) := by
  with_unfolding_all rfl
-- Shared pointer copies may alias one another and the caller's reference.
example : ∃ owners, FieldsFootprint world.memory (packets.map Prod.fst) owners ∧
    OwnerFrame world (owners ++ (afterArgs.owners world ++ (callerOwners world [caller] ++ []))) :=
  operands_owner_frame active_valid args owner_frame args_step
example : afterArgs.owners world = [1] := by decide +kernel
example : ∃ owners, Footprint world.memory (.node .tuple 0 (packets.map Prod.fst)) owners ∧
    OwnerFrame world (owners ++ (afterArgs.owners world ++ (callerOwners world [caller] ++ []))) := by
  have he : expression world active.roots [3] active.state (.aggregate .tuple 0 args) =
      some ((.node .tuple 0 (packets.map Prod.fst), .node .tuple 0 (packets.map Prod.snd)), afterArgs.state) := by
    simp only [Addressed.expression, args_step, Bind.bind, Option.bind]
  exact expression_owner_frame active_valid owner_frame he

private def assigned : Activation := { afterMove with state := afterMove.state.set 0 (.boxed (.number 7)) }
private def assignedWorld := world.write 4 (.owned 0)
private theorem assign_step : Derived.assign world active [caller] 0 (.use (.move payload)) = some (assignedWorld, assigned) := by
  with_unfolding_all rfl
private theorem assigned_frame : OwnerFrame assignedWorld (assigned.owners assignedWorld ++ (callerOwners assignedWorld [caller] ++ [])) :=
  Derived.assign_caller_owner_frame active_valid (by simpa using caller_valid) well_formed owner_frame assign_step
example : BoxCoverage assignedWorld (assigned.owners assignedWorld ++ (callerOwners world [caller] ++ [])) :=
  Derived.assign_box_coverage active_valid coverage assign_step
example : assigned.owners assignedWorld = [0, 1, 3] ∧ assignedWorld.memory[1]? = some (.owned 0) ∧
    assignedWorld.memory[6]? = world.memory[6]? := ⟨by decide +kernel, rfl, rfl⟩

private def droppedWorld := assignedWorld.retire [0]
private def dropped : Activation := { assigned with state := assigned.state.set 0 .empty }
private theorem drop_step : Derived.drop assignedWorld assigned [caller] 0 = some (droppedWorld, dropped) := by
  with_unfolding_all rfl

-- Dropping the moved inner Box does not retire its remaining outer shell,
-- sibling, shared aliases or caller owner. The complete destroyed ledger is exact.
example : ∃ discarded, droppedWorld = assignedWorld.retire discarded ∧
    discarded.length = (assigned.state 0).dropWork.boxes ∧
    (assigned.owners assignedWorld).Perm (discarded ++ dropped.owners droppedWorld) ∧
    OwnerFrame droppedWorld (dropped.owners droppedWorld ++ (callerOwners droppedWorld [caller] ++ [])) ∧
    BoxCoverage droppedWorld (dropped.owners droppedWorld ++ (callerOwners droppedWorld [caller] ++ [])) := by
  have assigned_spec := Derived.assign_spec active_valid (by simpa using caller_valid)
    well_formed (fun _ _ => none) 0 (.use (.move payload)) assign_step
  apply Derived.drop_owner_resources assigned_spec.2.2.2.2.1 assigned_spec.2.2.2.2.2.1
    assigned_spec.2.2.2.2.2.2.1 assigned_frame _ drop_step
  simpa only [show callerOwners assignedWorld [caller] = callerOwners world [caller] by decide +kernel] using
    Derived.assign_box_coverage active_valid coverage assign_step
example : dropped.owners droppedWorld = [1, 3] ∧ (List.range 9).map droppedWorld.live =
    [false, true, true, true, true, true, true, true, true] := by decide +kernel

-- A successful actual native call consumes the ownership boundary theorem.
example : ∃ final after cost current suspended packets masks remainder binding middle returned work owners,
    Derived.call (Helpers.callee 1 0) world active [caller] .boxNew [.move payload] 0 = some (final, after, cost) ∧
    active.scan world = some current ∧ scanCallers world [caller] = some suspended ∧
    operands world active.roots (current.loans ++ suspended.reads) active.state [.move payload] = some (packets, masks) ∧
    ({ active with state := masks } : Activation).scanExcept world 0 = some remainder ∧
    active.roots 0 = some binding ∧
    Helpers.callee 1 0 world ((remainder.reads ++ suspended.reads) ++ [binding.address])
      ({ active with state := masks } :: [caller]) .boxNew packets = some (middle, returned, work) ∧
    FieldsFootprint world.memory (packets.map Prod.fst) owners ∧
    OwnerFrame world (owners ++ (callerOwners world ({ active with state := masks } :: [caller]) ++ [])) := by
  have hs : (Derived.call (Helpers.callee 1 0) world active [caller] .boxNew [.move payload] 0).isSome = true := by decide +kernel
  obtain ⟨⟨final, after, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨current, suspended, packets, masks, remainder, binding, middle, returned, work, owners, ht⟩ :=
    Derived.call_argument_owner_frame active_valid owner_frame hr
  exact ⟨final, after, cost, current, suspended, packets, masks, remainder, binding, middle, returned, work, owners, hr, ht⟩

private theorem box_ready : Calling.ReadyAt Derived.TypedReady world active [caller] (.call .boxNew [.move payload] 0) := by
  intro current suspended packets masks _ _ hargs
  obtain ⟨_, guards, frame⟩ := active_valid
  obtain ⟨_, source, _, _, _⟩ := Addressed.operands_spec frame [.move payload] hargs
  have known : SourceEval.operands active.state [.move payload] = some ([.boxed (.number 7)], afterMove.state) := by
    with_unfolding_all rfl
  rw [known] at source
  have values := (Prod.mk.inj (Option.some.inj source)).1
  refine ⟨[.owned .u32], .owned (.owned .u32), ?_, ?_⟩
  · rw [← values]
    exact .cons (.owned (.number (by decide +kernel))) .nil
  · with_unfolding_all rfl

-- The complete actual call transfers the nested payload into the new Box,
-- stores it, and retains enclosing/sibling/caller owners and shared aliases.
example : ∃ final after cost,
    Derived.call (Helpers.callee 1 0) world active [caller] .boxNew [.move payload] 0 = some (final, after, cost) ∧
    OwnerFrame final (after.owners final ++ (callerOwners final [caller] ++ [])) ∧
    BoxCoverage final (after.owners final ++ (callerOwners final [caller] ++ [])) := by
  have hs : (Derived.call (Helpers.callee 1 0) world active [caller] .boxNew [.move payload] 0).isSome = true := by decide +kernel
  obtain ⟨⟨final, after, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨final, after, cost, hr, Derived.call_owner_resources (Helpers.callee_typed_respects 1 0)
    (Helpers.callee_owns 1 0) active_valid (by simpa using caller_valid) well_formed .boxNew [.move payload] 0
    owner_frame coverage box_ready hr⟩
example : (Derived.call (Helpers.callee 1 0) world active [caller] .boxNew [.move payload] 0).map
    (fun (final, after, _) => (after.owners final, callerOwners final [caller], final.live 9)) =
    some ([0, 9, 1, 3], [7], true) := by decide +kernel

-- Successful graph scanning does not certify unique ownership occurrences.
private def aliasedWorld := world.write 2 (.node .tuple 0 [.owned 1, .owned 1])
private def aliased : Activation := { active with
  state := active.state.set 1 (.node .tuple 0 [.boxed (.boxed (.number 7)), .boxed (.boxed (.number 7))]) }
example : (aliased.scan aliasedWorld).isSome = true := by decide +kernel
example : aliased.owners aliasedWorld = [0, 1, 0, 1] := by decide +kernel
example : ¬ OwnerFrame aliasedWorld (aliased.owners aliasedWorld ++ callerOwners aliasedWorld [caller]) := by
  intro h
  have hn := h.unique
  rw [show aliased.owners aliasedWorld ++ callerOwners aliasedWorld [caller] = [0, 1, 0, 1, 7] by decide +kernel] at hn
  exact (by decide +kernel : ¬ ([0, 1, 0, 1, 7] : List Nat).Nodup) hn

end SourceOwnerFramesTests


namespace SourceOwnerReturnTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval SourceEval.Addressed

private def world : World := ⟨[.number 7, .owned 0, .number 99], fun a =>
  if a = 0 then some .box else if a = 1 then some (.stack 10 0 1)
  else if a = 2 then some (.stack 20 0 2) else none, fun a => decide (a < 3)⟩
private def active : Activation := ⟨10, 1, fun s => if s = 0 then some ⟨1, 1⟩ else none,
  fun s => if s = 0 then .boxed (.number 7) else .empty⟩
private def caller : Activation := ⟨20, 1, fun s => if s = 0 then some ⟨2, 2⟩ else none,
  fun s => if s = 0 then .number 99 else .empty⟩
private def after : Activation := { active with state := active.state.set 0 .empty }
private def packet : ValueCell := (.owned 0, .boxed (.number 7))
private def final := world.retire [1]

private theorem active_valid : active.Valid world := by
  refine ⟨?_, [0, 1], ?_, ?_⟩
  · intro slot hs
    change 1 ≤ slot at hs
    simp [active, show slot ≠ 0 by omega]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
  · intro slot
    by_cases hz : slot = 0
    · subst slot
      exact ⟨_, [0], rfl, rfl, .owned rfl (.number 7), by simp⟩
    · simp [active, hz]
private theorem caller_valid : caller.Valid world := by
  refine ⟨?_, [2], ?_, ?_⟩
  · intro slot hs
    change 1 ≤ slot at hs
    simp [caller, show slot ≠ 0 by omega]
  · intro a ha
    have he : a = 2 := by simpa using ha
    subst a
    rfl
  · intro slot
    by_cases hz : slot = 0
    · subst slot
      exact ⟨_, [], rfl, rfl, .number 99, by simp⟩
    · simp [caller, hz]
private theorem well_formed : world.WellFormed := by
  constructor
  · intro a
    change ((if a = 0 then some Class.box else if a = 1 then some (.stack 10 0 1)
      else if a = 2 then some (.stack 20 0 2) else none).isSome = true ↔ a < 3)
    split_ifs <;> simp_all
    omega
  · intro a ha
    exact of_decide_eq_true ha
private theorem frame : OwnerFrame world (active.owners world ++ (callerOwners world [caller] ++ [])) := by
  rw [show active.owners world ++ (callerOwners world [caller] ++ []) = [0] by decide +kernel]
  exact ⟨by decide +kernel, by simp [BoxOwners, world], by simp [AliveOn, world]⟩
private theorem return_step : Derived.returnValue [caller] world active = some (.returned world after packet, .local 1) := by
  with_unfolding_all rfl
example : ∃ rest returned owners, Derived.Flow.returned world after packet = .returned world rest returned ∧
    Footprint world.memory returned.1 owners ∧
    OwnerFrame world (owners ++ (rest.owners world ++ (callerOwners world [caller] ++ []))) ∧
    (active.owners world).Perm (owners ++ rest.owners world) :=
  Derived.returnValue_owner_frame active_valid frame return_step

private theorem after_valid : after.Valid world := by
  have h := Derived.returnValue_spec active_valid (by simpa using caller_valid) well_formed return_step
  exact h.2.2.2.2.1.active
private theorem packet_readable : Readable world.memory world.live packet.1 packet.2 :=
  ⟨[0], .owned rfl (.number 7), by simp [AliveOn, world]⟩
private theorem packet_owners : Footprint world.memory packet.1 [0] := .owned rfl (.number 7)
private theorem close_step : close world after [caller] [] packet = some final := by with_unfolding_all rfl

-- Closing the actual returned frame retires its stack root, retaining its Box
-- and all caller bytes. Complete live-Box coverage survives the closure.
example : Footprint final.memory packet.1 [0] ∧
    OwnerFrame final ([0] ++ (callerOwners final [caller] ++ [])) ∧
    BoxCoverage final ([0] ++ (callerOwners final [caller] ++ [])) := by
  apply close_owner_transfer after_valid (by simpa using caller_valid) well_formed packet_readable packet_owners
  · rw [show after.owners world = [] by decide +kernel]
    simpa only [show active.owners world = [0] by decide +kernel, List.nil_append] using frame
  · rw [show after.owners world ++ (callerOwners world [caller] ++ []) = [] by decide +kernel]
    intro a hc _
    change (if a = 0 then some Class.box else _) = some .box at hc
    split_ifs at hc with h <;> simp_all
  · exact close_step
example : (List.range 3).map final.live = [true, false, true] := by decide +kernel
example : final.memory[2]? = world.memory[2]? := rfl

end SourceOwnerReturnTests
