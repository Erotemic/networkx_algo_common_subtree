module

public import SubtreeProofs.Rust.SourceOwnerActions
public import SubtreeProofs.Rust.SourceHeapOwnerDrivers

/-! Lift exact helper output ledgers over mixed stack/Box worlds. Every fresh
suffix identity is live Box-class storage; retained owners stay separated from
that suffix. Coverage accounts for all new Boxes, without deduplicating lists. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap Heap.Owners

theorem OwnerFrame.boxSuffix {world : World} {memory : Memory} {owners : List Nat}
    (h : OwnerFrame world owners) (hw : world.WellFormed) (he : Extends world.memory memory) :
    OwnerFrame (world.boxSuffix memory) (owners ++ fresh world.memory memory) := by
  have old := h.keep (world.boxSuffix_keeps hw he owners)
  have hb : ∀ a ∈ owners, a < world.memory.length := fun a ha => hw.2 a (h.alive a ha)
  have bounds : ∀ a ∈ fresh world.memory memory, world.memory.length ≤ a ∧ a < memory.length := by
    intro a ha
    have hi := List.mem_range'_1.mp ha
    have hlen := he.length_le
    exact ⟨hi.1, by omega⟩
  refine ⟨h.unique.append List.nodup_range' ?_, ?_, ?_⟩
  · apply List.disjoint_left.mpr
    intro a ha hf
    have hlo := (bounds a hf).1
    have hlt := hb a ha
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact old.classified a ha
    · exact (world.boxSuffix_fresh memory (bounds a ha).1 (bounds a ha).2).1
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact old.alive a ha
    · exact (world.boxSuffix_fresh memory (bounds a ha).1 (bounds a ha).2).2

theorem BoxCoverage.boxSuffix {world : World} {memory : Memory} {owners : List Nat}
    (h : BoxCoverage world owners) (hw : world.WellFormed) (he : Extends world.memory memory) :
    BoxCoverage (world.boxSuffix memory) (owners ++ fresh world.memory memory) := by
  intro a hc hl
  by_cases hb : a < world.memory.length
  · simp only [World.boxSuffix, hb, ite_true] at hc hl
    exact List.mem_append_left _ (h a hc hl)
  · have hi := (hw.boxSuffix he).2 a hl
    change a < memory.length at hi
    exact List.mem_append_right _ (List.mem_range'_1.mpr ⟨by omega, by
      have hlen := he.length_le
      omega⟩)

theorem boxSuffix_owner_transfer {world : World} {memory : Memory} {input output external : List Nat}
    (hw : world.WellFormed) (he : Extends world.memory memory)
    (hp : output.Perm (input ++ fresh world.memory memory))
    (hf : OwnerFrame world (input ++ external)) (covered : BoxCoverage world (input ++ external)) :
    OwnerFrame (world.boxSuffix memory) (output ++ external) ∧
      BoxCoverage (world.boxSuffix memory) (output ++ external) := by
  have out : (output ++ external).Perm ((input ++ external) ++ fresh world.memory memory) := by
    have swap : ((input ++ fresh world.memory memory) ++ external).Perm
        ((input ++ external) ++ fresh world.memory memory) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := fresh world.memory memory) (l₂ := external)).append_left input
    exact (hp.append_right external).trans swap
  exact ⟨(hf.boxSuffix hw he).perm out.symm, (covered.boxSuffix hw he).perm out.symm⟩

theorem World.WellFormed.outside {world : World} (hw : world.WellFormed) {address : Nat}
    (hb : ¬ address < world.memory.length) : world.classes address = none ∧ world.live address = false := by
  constructor
  · cases hc : world.classes address with
    | none => rfl
    | some kind => exact False.elim (hb ((hw.1 address).mp (by simp only [hc, Option.isSome_some])))
  · apply Bool.eq_false_iff.mpr
    intro hl
    exact hb (hw.2 address hl)

theorem World.boxSuffix_self {world : World} (hw : world.WellFormed) : world.boxSuffix world.memory = world := by
  apply congrArg₂ (fun classes live => (⟨world.memory, classes, live⟩ : World))
  · funext a
    by_cases hb : a < world.memory.length
    · simp only [hb, ite_true]
    · simp only [hb, ite_false, hw.outside hb |>.1]
  · funext a
    by_cases hb : a < world.memory.length
    · simp only [hb, ite_true]
    · simp only [hb, ite_false, decide_false, hw.outside hb |>.2]

theorem World.allocate_boxSuffix {world : World} (hw : world.WellFormed) (cell : Cell) :
    world.allocate .box cell = world.boxSuffix (world.memory ++ [cell]) := by
  apply congrArg₂ (fun classes live => (⟨world.memory ++ [cell], classes, live⟩ : World))
  · funext a
    by_cases hb : a < world.memory.length
    · simp only [hb, ite_true, show a ≠ world.memory.length by omega, ite_false]
    · by_cases he : a = world.memory.length
      · subst a
        simp
      · have ha : ¬a < world.memory.length + 1 := by omega
        simp only [hb, he, ite_false, List.length_append, List.length_singleton, ha, hw.outside hb |>.1]
  · funext a
    by_cases hb : a < world.memory.length
    · simp only [hb, ite_true, show a ≠ world.memory.length by omega, ite_false]
    · by_cases he : a = world.memory.length
      · subst a
        simp
      · have ha : ¬a < world.memory.length + 1 := by omega
        simp only [hb, he, ite_false, List.length_append, List.length_singleton, ha,
          decide_false, hw.outside hb |>.2]

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
