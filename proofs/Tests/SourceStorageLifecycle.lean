import SubtreeProofs.Rust.SourceActivationInitial
import SubtreeProofs.Rust.SourceEvalDerivedActions
import SubtreeProofs.Rust.SourceEvalTypeCertificate

namespace SourceStorageLifecycleTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed

private def base : World := ⟨[.number 7], fun a => if a = 0 then some .box else none, fun a => decide (a = 0)⟩
private def packets : List ValueCell :=
  [(.owned 0, .boxed (.number 7)), (.shared ⟨0, []⟩, .reference (.number 7)), (.number 9, .number 9)]
private def world := base.stackCells 10 (packets.map Prod.fst)
private def active := initialActivation base 10 5 packets

private theorem well_formed : base.WellFormed := by
  constructor
  · intro a
    by_cases hz : a = 0 <;> simp [base, hz]
  · intro a hl
    simpa [base] using hl

private theorem readable : ∀ p ∈ packets, Readable base.memory base.live p.1 p.2 := by
  intro p hp
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨[0], .owned rfl (.number 7), by simp [AliveOn, base]⟩
  · exact ⟨[0], .shared rfl (.number 7), by simp [AliveOn, base]⟩
  · exact ⟨[], .number 9, by simp [AliveOn]⟩

private theorem active_valid : active.Valid world := initialActivation_valid well_formed 10 5 readable (by decide +kernel)
private theorem world_valid : world.WellFormed := well_formed.stackCells _ _

example : enter base 10 5 packets = some (world, active) :=
  (enter_complete well_formed 10 5 readable (by decide +kernel)).1
example : active.state = SourceEval.initialState (packets.map Prod.snd) := rfl
example : active.roots 0 = none ∧ active.roots 1 = some ⟨1, 1⟩ ∧ active.roots 3 = some ⟨3, 3⟩ ∧ active.roots 4 = none := by decide +kernel
example : enter base 10 3 packets = none := by decide +kernel
example : (enter (base.retire [0]) 10 5 packets).isNone = true := by decide +kernel

-- This consumes the parsed definition's actual local count and signature
-- boundary; no count guessed from an example execution is an input.
example (decl : SourceEval.TypeReader.Definition) (hw : World) (hworld : hw.WellFormed)
    (frame : Nat) (args : List ValueCell)
    (hargs : ∀ p ∈ args, Readable hw.memory hw.live p.1 p.2)
    (hcount : args.length = (SourceEval.Types.inputs decl.source.function).length) :
    ∃ final entered, enter hw frame decl.source.localCount args = some (final, entered) ∧
      entered.Valid final ∧ entered.state = SourceEval.initialState (args.map Prod.snd) := by
  have h := enter_definition hworld frame decl hargs hcount
  exact ⟨_, _, h.1, h.2.1, rfl⟩

-- The same constructor covers every declaration read from the pinned actual
-- source, including the evaluator's full local layout.
example : ∃ program, SourceEval.TypeReader.read SourceEval.Input.Program.source 512 = .ok program ∧
    ∀ decl ∈ program.definitions, ∀ (hw : World) (frame : Nat) (args : List ValueCell),
      hw.WellFormed → (∀ p ∈ args, Readable hw.memory hw.live p.1 p.2) →
      args.length = (SourceEval.Types.inputs decl.source.function).length →
      ∃ final entered, enter hw frame decl.source.localCount args = some (final, entered) ∧
        entered.Valid final ∧ entered.state = SourceEval.initialState (args.map Prod.snd) := by
  obtain ⟨program, hr, _, _, _⟩ := SourceEval.TypeReader.Certificate.original_declarations
  refine ⟨program, hr, ?_⟩
  intro decl _ hw frame args hworld hargs hcount
  have h := enter_definition hworld frame decl hargs hcount
  exact ⟨_, _, h.1, h.2.1, rfl⟩

-- The active reference protects Box zero; an owned Box cannot silently end
-- storage. The initialized shared local itself can end storage with no drop.
example : Derived.drop world active [] 1 = none := by decide +kernel
example : Derived.storageDead world active [] 1 = none := by decide +kernel
example : (Derived.storageDead world active [] 2).isSome = true := by decide +kernel
example : Derived.storageLive world active [] 1 = none := by decide +kernel
example : Derived.storageLive world active [] 5 = none := by decide +kernel

private def instructions : List SourceEval.Action := [
  .storageDead 2, .drop 1, .storageDead 1, .drop 3, .storageDead 3,
  .storageLive 4, .assign 4 (.use (.number 23)), .fakeRead (.local 4),
  .drop 4, .storageDead 4, .storageLive 4, .assign 4 (.use (.number 24))]

private theorem run_some : (Derived.actions world active [] instructions).isSome = true := by decide +kernel

-- One chain consumes the old owner, tears down parameter storage, then opens,
-- initializes, drops, retires and reopens the same local at a fresh generation.
-- Destruction visits are included once in work.steps, while Box count is exact.
example : (Derived.actions world active [] instructions).map (fun (final, after, cost) =>
    (final.memory.length, (List.range 6).map final.live, after.roots 4,
      cost.work.steps, cost.destroyed.visits, cost.destroyed.boxes)) =
    some (6, [false, false, false, false, false, true], some ⟨5, 5⟩, 18, 4, 1) := by decide +kernel

example : ∃ final after cost,
    Derived.actions world active [] instructions = some (final, after, cost) ∧
    (∀ call, SourceEval.exec call (instructions.foldr Control.Tree.step .done) active.state = some (.next after.state, cost)) ∧
    after.Valid final ∧ final.WellFormed := by
  obtain ⟨result, hr⟩ := Option.isSome_iff_exists.mp run_some
  rcases result with ⟨final, after, cost⟩
  have h := Derived.actions_spec active_valid (by simp) world_valid instructions hr
  exact ⟨final, after, cost, hr, h.1, h.2.2.2.1, h.2.2.2.2.2⟩

-- The caller points to scalar local three, which has no Box owners at all.
-- Both drop and storage-dead must still reject invalidating its stack root.
private def callerPackets : List ValueCell := [(.shared ⟨3, []⟩, .reference (.number 9))]
private def withCaller := world.stackCells 20 (callerPackets.map Prod.fst)
private def caller := initialActivation world 20 2 callerPackets

private theorem caller_readable : ∀ p ∈ callerPackets, Readable world.memory world.live p.1 p.2 := by
  intro p hp
  have he : p = (.shared ⟨3, []⟩, .reference (.number 9)) := by simpa [callerPackets] using hp
  subst p
  exact ⟨[3], .shared rfl (.number 9), by simp [AliveOn, world, World.stackCells, base, packets]⟩
private theorem caller_valid : caller.Valid withCaller := initialActivation_valid world_valid 20 2 caller_readable (by decide +kernel)
private theorem active_with_caller : active.Valid withCaller := by
  obtain ⟨hb, guards, hf⟩ := active_valid
  exact ⟨hb, guards, hf.keep (world.stackCells_keeps world_valid _ _ _)⟩

example : Derived.drop withCaller active [caller] 3 = none := by decide +kernel
example : Derived.storageDead withCaller active [caller] 3 = none := by decide +kernel
example : (Derived.drop withCaller active [] 3).isSome = true := by decide +kernel
example : (Derived.storageDead withCaller active [] 3).isSome = true := by decide +kernel

-- Operations on unrelated storage retain the exact computed caller inventory.
example : ∃ final after,
    Derived.storageDead withCaller active [caller] 2 = some (final, after) ∧
    after.Valid final ∧ caller.Valid final ∧
    ∃ r, scanCallers withCaller [caller] = some r ∧ Callers final [caller] r := by
  have hs : (Derived.storageDead withCaller active [caller] 2).isSome = true := by decide +kernel
  obtain ⟨⟨final, after⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have h := (Derived.storageDead_spec active_with_caller (by simpa using caller_valid)
    (world_valid.stackCells _ _) hr).1
  exact ⟨final, after, hr, h.valid, h.callers caller (by simp), h.suspended⟩

-- Duplicate owner occurrences and a stack root disguised as a Box are separate
-- rejections. A retained read graph alone does not certify either property.
private def duplicatePackets : List ValueCell := [
  (.node .tuple 0 [.owned 0, .owned 0], .node .tuple 0 [.boxed (.number 7), .boxed (.number 7)])]
private def duplicateWorld := base.stackCells 10 (duplicatePackets.map Prod.fst)
private def duplicateActive := initialActivation base 10 2 duplicatePackets
example : Derived.drop duplicateWorld duplicateActive [] 1 = none := by decide +kernel
private def wrongClassBase : World := { base with classes := fun a => if a = 0 then some (.stack 99 0 0) else none }
private def wrongClassWorld := wrongClassBase.stackCells 10 [Cell.owned 0]
private def wrongClassActive := initialActivation wrongClassBase 10 2 [(.owned 0, .boxed (.number 7))]
example : Derived.drop wrongClassWorld wrongClassActive [] 1 = none := by decide +kernel

end SourceStorageLifecycleTests
