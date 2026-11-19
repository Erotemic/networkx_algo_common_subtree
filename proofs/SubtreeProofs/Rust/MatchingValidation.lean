module

public import SubtreeProofs.Rust.MatchingCostConstruction
import Mathlib.Tactic

/-!
# Actual rectangular-matrix validation for signed partial matching

Every represented optional-weight matrix is checked safely. The returned
boolean equals the independent fixed-width predicate, including early false
returns and zero-row/zero-column cases.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingValidation

def Rectangular (weights : Slice (alloc.vec.Vec (Option I64))) (right : Nat) : Prop :=
  ∀ row ∈ weights.val, row.length = right

theorem rectangular_iff_index (weights : Slice (alloc.vec.Vec (Option I64))) (right : Nat) :
    Rectangular weights right ↔ ∀ index < weights.length, (weights.val[index]!).length = right := by
  constructor
  · intro h index hi
    apply h
    rw [getElem!_pos weights.val index hi]
    exact List.getElem_mem hi
  · intro h row hr
    obtain ⟨index,hi,he⟩ := List.mem_iff_getElem.mp hr
    have hh := h index hi
    rw [getElem!_pos weights.val index hi,he] at hh
    exact hh

/-- The complete actual validator loop checks exactly the represented rows. -/
theorem is_rectangular_loop_spec (weights : Slice (alloc.vec.Vec (Option I64))) (right row : Usize)
    (hrow : row.val ≤ weights.length) (hprefix : ∀ index < row.val, (weights.val[index]!).length = right.val) :
    matching.is_rectangular_loop weights right row ⦃ result => result = true ↔ Rectangular weights right.val ⦄ := by
  unfold matching.is_rectangular_loop
  apply loop.spec_decr_nat (fun current => weights.length-current.val)
    (fun current => current.val ≤ weights.length ∧ ∀ index < current.val, (weights.val[index]!).length = right.val)
    (fun result => result = true ↔ Rectangular weights right.val) _ row ?_ ⟨hrow,hprefix⟩
  intro current hinv
  rcases hinv with ⟨hbound,hchecked⟩
  have hn := Slice.len_val weights
  unfold matching.is_rectangular_loop.body
  dsimp only
  split
  · rename_i hr
    have hi : current.val < weights.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec weights current hi)
    intro inputRow hInputRow
    have hinput : inputRow = weights.val[current.val]! := by
      simpa only [getElem!_pos weights.val current.val hi] using hInputRow
    by_cases hw : inputRow.length = right.val
    · have he : alloc.vec.Vec.len inputRow = right := by
        apply UScalar.eq_of_val_eq
        simpa only [alloc.vec.Vec.len_val] using hw
      simp only [he,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
      apply WP.spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
      intro next hNext
      have hnext : next.val = current.val+1 := by simpa using hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by omega,?_⟩,by omega⟩
      intro index hb
      by_cases hsame : index = current.val
      · subst index
        simpa only [hinput] using hw
      · exact hchecked index (by omega)
    · have hne : alloc.vec.Vec.len inputRow ≠ right := by
        intro he
        apply hw
        simpa only [alloc.vec.Vec.len_val] using congrArg UScalar.val he
      have hnot : ¬ Rectangular weights right.val := by
        intro hrect
        apply hw
        have hm : inputRow ∈ weights.val := by rw [hInputRow]; exact List.getElem_mem hi
        exact hrect inputRow hm
      have hbranch : (alloc.vec.Vec.len inputRow != right) = true := bne_iff_ne.mpr hne
      simpa only [hbranch,↓reduceIte,WP.spec_ok,Bool.false_eq_true,false_iff] using hnot
  · rename_i hr
    simp only [WP.spec_ok,eq_self,true_iff]
    apply (rectangular_iff_index weights right.val).mpr
    intro index hi
    exact hchecked index (by scalar_tac)

/-- Actual rectangular validation safely decides the independent predicate
for every represented matrix and requested width. -/
theorem is_rectangular_spec (weights : Slice (alloc.vec.Vec (Option I64))) (right : Usize) :
    matching.is_rectangular weights right ⦃ result => result = true ↔ Rectangular weights right.val ⦄ := by
  exact is_rectangular_loop_spec weights right 0#usize (by simp) (by simp)

end SubtreeProofs.Rust.MatchingValidation

end
