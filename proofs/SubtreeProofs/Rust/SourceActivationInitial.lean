module

public import SubtreeProofs.Rust.SourceEvalDerivedDrop
public import SubtreeProofs.Rust.SourceEvalTypeReader

/-! Addressable argument storage follows the actual source convention: return
local zero is initially absent, arguments occupy locals one through their arity,
and the activation bound comes from the parsed local declaration count. Fresh
symbolic stack roots preserve existing cells, classes, liveness and caller data. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap SourceEval.Addressed

def World.stackCells (world : World) (frame : Nat) (cells : List Cell) : World :=
  ⟨world.memory ++ cells,
    fun a => if a < world.memory.length then world.classes a
      else if a < world.memory.length + cells.length then
        some (.stack frame (a - world.memory.length + 1) a) else none,
    fun a => if a < world.memory.length then world.live a
      else decide (a < world.memory.length + cells.length)⟩

theorem World.stackCells_keeps {world : World} (hw : world.WellFormed) (frame : Nat) (cells : List Cell) (guards : List Nat) :
    Keeps world (world.stackCells frame cells) guards := by
  refine ⟨Extends.append _ _, ?_, ?_⟩
  · intro a kind hc
    have hb := (hw.1 a).mp (by simp [hc])
    simp only [stackCells, hb, ite_true, hc]
  · intro a _ hl
    simp only [stackCells, hw.2 a hl, ite_true, hl]

theorem World.WellFormed.stackCells {world : World} (hw : world.WellFormed) (frame : Nat) (cells : List Cell) :
    (world.stackCells frame cells).WellFormed := by
  constructor
  · intro a
    by_cases hb : a < world.memory.length
    · simp only [World.stackCells, hb, ite_true, List.length_append]
      exact ⟨fun _ => by omega, fun _ => (hw.1 a).mpr hb⟩
    · simp only [World.stackCells, hb, ite_false, List.length_append]
      split <;> simp_all
  · intro a hl
    by_cases hb : a < world.memory.length
    · have ha := hw.2 a (by simpa only [World.stackCells, hb, ite_true] using hl)
      simp only [World.stackCells, List.length_append]
      omega
    · simpa only [World.stackCells, hb, ite_false, decide_eq_true_eq, List.length_append] using hl

def argumentRoots (base count : Nat) : Roots := fun slot =>
  if 0 < slot ∧ slot ≤ count then some ⟨base + (slot - 1), base + (slot - 1)⟩ else none

def packetReads (world : World) (packets : List ValueCell) : List Nat :=
  packets.flatMap fun packet => (traceGraph world.memory packet.1 packet.2).getD []

theorem packetReads_spec {world : World} {packets : List ValueCell}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) :
    AliveOn world.live (packetReads world packets) ∧
      ∀ p ∈ packets, ∃ used, Graph world.memory p.1 p.2 used ∧ used ⊆ packetReads world packets := by
  constructor
  · intro a ha
    obtain ⟨p, hm, hh⟩ := List.mem_flatMap.mp ha
    obtain ⟨used, hg, hl⟩ := hp p hm
    exact hl a (by simpa only [hg.trace, Option.getD_some] using hh)
  · intro p hm
    obtain ⟨used, hg, _⟩ := hp p hm
    refine ⟨used, hg, ?_⟩
    intro a ha
    exact List.mem_flatMap.mpr ⟨p, hm, by simpa only [hg.trace, Option.getD_some] using ha⟩

def initialActivation (world : World) (frame count : Nat) (packets : List ValueCell) : Activation :=
  ⟨frame, count, argumentRoots world.memory.length packets.length, SourceEval.initialState (packets.map Prod.snd)⟩

theorem initialActivation_valid {world : World} (hw : world.WellFormed) (frame count : Nat) {packets : List ValueCell}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (bound : packets.length + 1 ≤ count) :
    (initialActivation world frame count packets).Valid (world.stackCells frame (packets.map Prod.fst)) := by
  have hk := world.stackCells_keeps hw frame (packets.map Prod.fst) (packetReads world packets)
  obtain ⟨halive, hgraphs⟩ := packetReads_spec hp
  refine ⟨?_, packetReads world packets ++ List.range' world.memory.length packets.length, ?_, ?_⟩
  · intro slot hs
    change count ≤ slot at hs
    have hn : ¬ (0 < slot ∧ slot ≤ packets.length) := by omega
    simp only [initialActivation, argumentRoots, hn, ite_false]
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hk.alive a ha (halive a ha)
    · have hb := List.mem_range'_1.mp ha
      simp only [World.stackCells, show ¬a < world.memory.length by omega, ite_false, decide_eq_true_eq, List.length_map]
      omega
  · intro slot
    change match argumentRoots world.memory.length packets.length slot with
      | none => SourceEval.initialState (packets.map Prod.snd) slot = .empty
      | some binding => Anchored (world.stackCells frame (packets.map Prod.fst)) frame slot binding
          (SourceEval.initialState (packets.map Prod.snd) slot)
          (packetReads world packets ++ List.range' world.memory.length packets.length)
    by_cases hs : 0 < slot ∧ slot ≤ packets.length
    · simp only [argumentRoots, hs]
      have hi : slot - 1 < packets.length := by omega
      let packet := packets[slot - 1]
      have hg : packets[slot - 1]? = some packet := List.getElem?_eq_getElem hi
      obtain ⟨used, hv, hsub⟩ := hgraphs packet (List.mem_of_getElem? hg)
      have hindex : world.memory.length + (slot - 1) - world.memory.length = slot - 1 := by omega
      have hcell : (world.stackCells frame (packets.map Prod.fst)).memory[world.memory.length + (slot - 1)]? = some packet.1 := by
        change (world.memory ++ packets.map Prod.fst)[world.memory.length + (slot - 1)]? = some packet.1
        rw [List.getElem?_append_right (show world.memory.length ≤ world.memory.length + (slot - 1) by omega)]
        simp only [hindex, List.getElem?_map, hg, Option.map_some]
      have hclass : (world.stackCells frame (packets.map Prod.fst)).classes (world.memory.length + (slot - 1)) =
          some (.stack frame slot (world.memory.length + (slot - 1))) := by
        simp only [World.stackCells, show ¬ world.memory.length + (slot - 1) < world.memory.length by omega,
          ite_false, List.length_map, show world.memory.length + (slot - 1) < world.memory.length + packets.length by omega,
          ite_true, hindex, show slot - 1 + 1 = slot by omega]
      have hstate : SourceEval.initialState (packets.map Prod.snd) slot = Slot.ofValue packet.2 := by
        simp only [SourceEval.initialState, Partial.Locals.lift, initialEnv, show slot ≠ 0 by omega,
          ite_false, List.getElem?_map, hg, Option.map_some]
      rw [hstate]
      refine ⟨packet.1, used, hcell, hclass, hv.partial.mono hk.memory, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_append_left _ (hsub ha)
      · apply List.mem_append_right
        have he := List.mem_singleton.mp ha
        change a = world.memory.length + (slot - 1) at he
        rw [he]
        exact List.mem_range'_1.mpr ⟨by omega, by omega⟩
    · simp only [argumentRoots, hs, ite_false]
      by_cases hz : slot = 0
      · simp only [SourceEval.initialState, Partial.Locals.lift, initialEnv, hz, ite_true]
      · have hi : packets.length ≤ slot - 1 := by omega
        simp only [SourceEval.initialState, Partial.Locals.lift, initialEnv, hz, ite_false,
          List.getElem?_map, List.getElem?_eq_none hi, Option.map_none]

def enter (world : World) (frame count : Nat) (packets : List ValueCell) : Option (World × Activation) :=
  if packets.length + 1 ≤ count ∧ packets.all (fun packet =>
      match traceGraph world.memory packet.1 packet.2 with
      | none => false
      | some used => used.all world.live) then
    some (world.stackCells frame (packets.map Prod.fst), initialActivation world frame count packets)
  else none

theorem enter_complete {world : World} (hw : world.WellFormed) (frame count : Nat) {packets : List ValueCell}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (bound : packets.length + 1 ≤ count) :
    enter world frame count packets =
        some (world.stackCells frame (packets.map Prod.fst), initialActivation world frame count packets) ∧
      (initialActivation world frame count packets).Valid (world.stackCells frame (packets.map Prod.fst)) ∧
      (world.stackCells frame (packets.map Prod.fst)).WellFormed ∧
      ∀ guards, Keeps world (world.stackCells frame (packets.map Prod.fst)) guards := by
  have hall : packets.all (fun packet => match traceGraph world.memory packet.1 packet.2 with
      | none => false | some used => used.all world.live) = true := by
    apply List.all_eq_true.mpr
    intro packet hm
    obtain ⟨used, hg, hl⟩ := hp packet hm
    simpa only [hg.trace] using List.all_eq_true.mpr hl
  exact ⟨by simp only [enter, bound, hall, and_self, ite_true],
    initialActivation_valid hw frame count hp bound, hw.stackCells _ _, world.stackCells_keeps hw _ _⟩

theorem enter_definition {world : World} (hw : world.WellFormed) (frame : Nat)
    (decl : SourceEval.TypeReader.Definition) {packets : List ValueCell}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (arity : packets.length = (SourceEval.Types.inputs decl.source.function).length) :
    enter world frame decl.source.localCount packets =
        some (world.stackCells frame (packets.map Prod.fst), initialActivation world frame decl.source.localCount packets) ∧
      (initialActivation world frame decl.source.localCount packets).Valid (world.stackCells frame (packets.map Prod.fst)) ∧
      (world.stackCells frame (packets.map Prod.fst)).WellFormed ∧
      ∀ guards, Keeps world (world.stackCells frame (packets.map Prod.fst)) guards := by
  have he := congrArg List.length decl.boundary
  have hb := List.length_take_le' ((SourceEval.Types.inputs decl.source.function).length + 1) decl.locals
  simp only [List.length_cons] at he
  apply enter_complete hw frame decl.source.localCount hp
  rw [decl.count] at hb
  omega

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
