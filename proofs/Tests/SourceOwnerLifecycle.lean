module

import SubtreeProofs.Rust.SourceOwnerActions
import all SubtreeProofs.Rust.SourceHeapGraphTrace
import all SubtreeProofs.Rust.SourceHeapResources
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceOwnerLifecycleTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed

private def base : World := ⟨[.number 7, .number 42, .owned 1], fun a =>
  if a = 0 ∨ a = 1 then some .box else if a = 2 then some (.stack 20 0 2) else none,
  fun a => decide (a < 3)⟩
private def caller : Activation := ⟨20, 1, fun s => if s = 0 then some ⟨2, 2⟩ else none,
  fun s => if s = 0 then .boxed (.number 42) else .empty⟩
private def packets : List ValueCell := [(.owned 0, .boxed (.number 7)),
  (.shared ⟨0, []⟩, .reference (.number 7)), (.number 9, .number 9)]
private def world := base.stackCells 10 (packets.map Prod.fst)
private def active := initialActivation base 10 5 packets

private theorem well_formed : base.WellFormed := by
  constructor
  · intro a
    change ((if a = 0 ∨ a = 1 then some Class.box else if a = 2 then some (.stack 20 0 2) else none).isSome = true ↔ a < 3)
    split_ifs <;> simp_all <;> omega
  · intro a ha
    exact of_decide_eq_true ha
private theorem caller_valid : caller.Valid base := by
  refine ⟨?_, [1, 2], ?_, ?_⟩
  · intro slot hs
    change 1 ≤ slot at hs
    simp [caller, show slot ≠ 0 by omega]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
  · intro slot
    by_cases he : slot = 0
    · subst slot
      exact ⟨_, [1], rfl, rfl, .owned rfl (.number 42), by simp⟩
    · simp [caller, he]
private theorem readable : ∀ p ∈ packets, Readable base.memory base.live p.1 p.2 := by
  intro p hp
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨[0], .owned rfl (.number 7), by simp [AliveOn, base]⟩
  · exact ⟨[0], .shared rfl (.number 7), by simp [AliveOn, base]⟩
  · exact ⟨[], .number 9, by simp [AliveOn]⟩
private theorem footprint : FieldsFootprint base.memory (packets.map Prod.fst) [0] :=
  .cons (.owned rfl (.number 7)) (.cons (.shared ⟨0, []⟩) (.cons (.number 9) .nil))
private theorem frame : OwnerFrame base ([0] ++ (callerOwners base [caller] ++ [])) := by
  rw [show [0] ++ (callerOwners base [caller] ++ []) = [0, 1] by decide +kernel]
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
private theorem coverage : BoxCoverage base ([0] ++ (callerOwners base [caller] ++ [])) := by
  rw [show [0] ++ (callerOwners base [caller] ++ []) = [0, 1] by decide +kernel]
  intro a hc _
  change (if a = 0 ∨ a = 1 then some Class.box else _) = some .box at hc
  split_ifs at hc with h <;> simp_all
private theorem enter_step : enter base 10 5 packets = some (world, active) :=
  (enter_complete well_formed 10 5 readable (by decide +kernel)).1
private theorem active_valid : active.Valid world := initialActivation_valid well_formed 10 5 readable (by decide +kernel)
private theorem world_valid : world.WellFormed := well_formed.stackCells _ _
private theorem caller_entered : caller.Valid world := by
  obtain ⟨bound, guards, frame⟩ := caller_valid
  exact ⟨bound, guards, frame.keep (base.stackCells_keeps well_formed _ _ _)⟩
private theorem entered_resources :
    OwnerFrame world (active.owners world ++ (callerOwners world [caller] ++ [])) ∧
    BoxCoverage world (active.owners world ++ (callerOwners world [caller] ++ [])) :=
  enter_owner_resources well_formed 10 5 (by simpa using caller_valid) readable footprint frame coverage enter_step

-- Both parameter cells and the actual caller retain their exact Box owners;
-- the input reference is allowed to point at the owned argument's Box.
example : active.owners world = [0] ∧ callerOwners world [caller] = [1] := by decide +kernel
example : Derived.drop world active [caller] 1 = none := by decide +kernel
example : Derived.storageDead world active [caller] 1 = none := by decide +kernel

private def instructions : List SourceEval.Action := [
  .storageDead 2, .drop 1, .storageDead 1, .drop 3, .storageDead 3,
  .storageLive 4, .assign 4 (.use (.number 23)), .drop 4, .storageDead 4,
  .storageLive 4, .assign 4 (.use (.number 24))]
private theorem run_some : (Derived.actions world active [caller] instructions).isSome = true := by decide +kernel
example : (Derived.actions world active [caller] instructions).map (fun (final, after, cost) =>
    (final.memory.length, (List.range 8).map final.live, (after.roots 4).map (fun b => (b.address, b.generation)),
      after.owners final, callerOwners final [caller], cost.work.steps, cost.destroyed.visits, cost.destroyed.boxes)) =
    some (8, [false, true, true, false, false, false, false, true], some (7, 7), [], [1], 17, 4, 1) := by with_unfolding_all rfl

-- One theorem consumes the actual entire sequence: every removed occurrence
-- is counted once, and final initialized/caller owners cover every live Box.
example : ∃ final after cost discarded,
    Derived.actions world active [caller] instructions = some (final, after, cost) ∧
    (active.owners world ++ (callerOwners world [caller] ++ [])).Perm
      (discarded ++ (after.owners final ++ (callerOwners final [caller] ++ []))) ∧
    discarded.length = cost.destroyed.boxes ∧ discarded.Nodup ∧
    OwnerFrame final (after.owners final ++ (callerOwners final [caller] ++ [])) ∧
    BoxCoverage final (after.owners final ++ (callerOwners final [caller] ++ [])) ∧
    (∀ address ∈ discarded, world.classes address = some .box ∧ final.classes address = some .box ∧
      world.live address = true ∧ final.live address = false) := by
  obtain ⟨⟨final, after, cost⟩, hr⟩ := Option.isSome_iff_exists.mp run_some
  obtain ⟨discarded, hp⟩ := Derived.actions_owner_destruction active_valid (by simpa using caller_entered)
    world_valid instructions entered_resources.1 entered_resources.2 hr
  exact ⟨final, after, cost, discarded, hr, hp⟩

-- Entry's read checks do not manufacture exclusive ownership for aliased
-- owning arguments. The explicit input OwnerFrame rejects duplicate owners.
private def duplicates : List ValueCell := [(.owned 0, .boxed (.number 7)), (.owned 0, .boxed (.number 7))]
example : (enter base 30 3 duplicates).isSome = true := by decide +kernel
example : ¬ OwnerFrame base ([0, 0] ++ callerOwners base [caller]) := by
  intro h
  have hn := h.unique
  rw [show [0, 0] ++ callerOwners base [caller] = [0, 0, 1] by decide +kernel] at hn
  exact (by decide +kernel : ¬ ([0, 0, 1] : List Nat).Nodup) hn

-- The real parsed declaration supplies its own arity/count. No substituted
-- declaration or desired output is an input to this ownership consumer.
example (decl : SourceEval.TypeReader.Definition) (world : World) (hw : world.WellFormed)
    (frame : Nat) (packets : List ValueCell) (callers : List Activation) (owners external : List Nat)
    (hc : ∀ a ∈ callers, a.Valid world) (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (hf : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (arity : packets.length = (SourceEval.Types.inputs decl.source.function).length) :
    ∃ final entered, enter world frame decl.source.localCount packets = some (final, entered) ∧
      OwnerFrame final (entered.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (entered.owners final ++ (callerOwners final callers ++ external)) := by
  have h := enter_definition hw frame decl hp arity
  exact ⟨_, _, h.1, enter_owner_resources hw frame decl.source.localCount hc hp ho hf covered h.1⟩

end SourceOwnerLifecycleTests
