module

public import SubtreeProofs.Rust.SourceHeapReadback
public import SubtreeProofs.Rust.SourceEvalAddressedChoice

/-! Lift an existing helper's Box-only memory suffix over a mixed stack/Box
world. Old cells/classes/live flags are retained exactly; fresh suffix cells
receive live Box identities. Ghost output metadata comes from concrete readback. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

theorem Extends.length_le {before after : Memory} (h : Extends before after) : before.length ≤ after.length := by
  by_contra hn
  have hi : after.length < before.length := by omega
  have hs := h after.length before[after.length] (List.getElem?_eq_getElem hi)
  have he : after[after.length]? = none := List.getElem?_eq_none (by omega)
  rw [he] at hs
  cases hs

end SubtreeProofs.Rust.LookupSource.Heap

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap SourceEval.Addressed

def World.boxSuffix (world : World) (memory : Memory) : World :=
  ⟨memory,
    fun a => if a < world.memory.length then world.classes a
      else if a < memory.length then some .box else none,
    fun a => if a < world.memory.length then world.live a else decide (a < memory.length)⟩

theorem World.boxSuffix_keeps {world : World} (hw : world.WellFormed) {memory : Memory}
    (he : Extends world.memory memory) (guards : List Nat) : Keeps world (world.boxSuffix memory) guards := by
  refine ⟨he, ?_, ?_⟩
  · intro a kind hc
    have hb := (hw.1 a).mp (by simp [hc])
    simp only [boxSuffix, hb, ite_true, hc]
  · intro a _ hl
    simp only [boxSuffix, hw.2 a hl, ite_true, hl]

theorem World.WellFormed.boxSuffix {world : World} (hw : world.WellFormed) {memory : Memory}
    (he : Extends world.memory memory) : (world.boxSuffix memory).WellFormed := by
  constructor
  · intro a
    by_cases hb : a < world.memory.length
    · simp only [World.boxSuffix, hb, ite_true]
      exact ⟨fun _ => by have hh := he.length_le; omega, fun _ => (hw.1 a).mpr hb⟩
    · simp only [World.boxSuffix, hb, ite_false]
      split <;> simp_all
  · intro a hl
    by_cases hb : a < world.memory.length
    · have hbound := he.length_le
      have ha := hw.2 a (by simpa only [World.boxSuffix, hb, ite_true] using hl)
      change a < memory.length
      omega
    · simpa only [World.boxSuffix, hb, ite_false, decide_eq_true_eq] using hl

theorem World.boxSuffix_old (world : World) (memory : Memory) {a : Nat} (ha : a < world.memory.length) :
    (world.boxSuffix memory).classes a = world.classes a ∧ (world.boxSuffix memory).live a = world.live a := by
  simp only [boxSuffix, ha, ite_true, and_self]

theorem World.boxSuffix_fresh (world : World) (memory : Memory) {a : Nat}
    (ha : world.memory.length ≤ a) (hb : a < memory.length) :
    (world.boxSuffix memory).classes a = some .box ∧ (world.boxSuffix memory).live a = true := by
  simp only [boxSuffix, show ¬a < world.memory.length by omega, ite_false, hb, ite_true, decide_true, and_self]

theorem BoxOwners.boxSuffix {world : World} (hw : world.WellFormed) {owners : List Nat}
    (ho : BoxOwners world owners) {memory : Memory} (he : Extends world.memory memory) :
    BoxOwners (world.boxSuffix memory) owners := by
  intro a ha
  exact (world.boxSuffix_keeps hw he []).classes a .box (ho a ha)

def readPacket (budget : Nat) (world : World) (cell : Cell) : Option ValueCell := do
  let (value, used) ← snapshot budget world.memory cell
  if used.all world.live then some (cell, value) else none

theorem readPacket_spec {budget : Nat} {world : World} {cell : Cell} {packet : ValueCell}
    (h : readPacket budget world cell = some packet) : packet.1 = cell ∧ Readable world.memory world.live packet.1 packet.2 := by
  unfold readPacket at h
  cases hs : snapshot budget world.memory cell with
  | none => simp [hs] at h
  | some pair =>
    rcases pair with ⟨value, used⟩
    simp only [hs, Bind.bind, Option.bind] at h
    split at h
    next live =>
      cases h
      exact ⟨rfl, used, snapshot_spec budget hs, List.all_eq_true.mp live⟩
    next => cases h

theorem readPacket_complete {world : World} {cell : Cell} {value : Value}
    (h : Readable world.memory world.live cell value) (budget : Nat) (bound : valueDepth value ≤ budget) :
    readPacket budget world cell = some (cell, value) := by
  obtain ⟨used, hg, hl⟩ := h
  simp only [readPacket, hg.snapshot budget bound, List.all_eq_true.mpr hl, ite_true, Bind.bind, Option.bind]

theorem readPacket_represents {budget : Nat} {world : World} {cell : Cell} {value : Value} {packet : ValueCell}
    (hv : Represents world.memory cell value) (h : readPacket budget world cell = some packet) :
    packet = (cell, value) ∧ Readable world.memory world.live cell value := by
  obtain ⟨hcell, used, hg, hl⟩ := readPacket_spec h
  have he := represents_unique (hcell ▸ hg.represents) hv
  rcases packet with ⟨raw, target⟩
  cases hcell
  cases he
  exact ⟨rfl, used, hg, hl⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
