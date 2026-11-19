module

public import SubtreeProofs.Rust.Generated.VerifiedAssignmentCore
import Mathlib.Tactic

/-!
# Actual square-matrix validation

The generated source validator safely terminates on every represented input.
Its boolean is true exactly when all supplied row lengths equal the number
of rows. Its early-false branch supplies an actual malformed input row.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentValidation

def Square (cost : Slice (alloc.vec.Vec I64)) : Prop := ∀ row ∈ cost.val, row.length = cost.length

theorem square_iff_index (cost : Slice (alloc.vec.Vec I64)) :
    Square cost ↔ ∀ index < cost.length, (cost.val[index]!).length = cost.length := by
  constructor
  · intro h index hi
    apply h
    rw [getElem!_pos cost.val index hi]
    exact List.getElem_mem hi
  · intro h row hr
    obtain ⟨index,hi,he⟩ := List.mem_iff_getElem.mp hr
    have hh := h index hi
    rw [getElem!_pos cost.val index hi,he] at hh
    exact hh

/-- The complete actual validation loop realizes the independent square
predicate from a correctly checked prefix, including early rejection. -/
theorem is_square_loop_spec (cost : Slice (alloc.vec.Vec I64)) (n row : Usize) (hn : n.val = cost.length)
    (hrow : row.val ≤ cost.length) (hprefix : ∀ index < row.val, (cost.val[index]!).length = cost.length) :
    is_square_loop cost n row ⦃ result => result = true ↔ Square cost ⦄ := by
  unfold is_square_loop
  apply loop.spec_decr_nat (fun current => cost.length-current.val)
    (fun current => current.val ≤ cost.length ∧ ∀ index < current.val, (cost.val[index]!).length = cost.length)
    (fun result => result = true ↔ Square cost) _ row ?_ ⟨hrow,hprefix⟩
  intro current hinv
  rcases hinv with ⟨hbound,hchecked⟩
  unfold is_square_loop.body
  by_cases hr : current.val < n.val
  · have hcurrent : current < n := hr
    simp only [hcurrent,↓reduceIte]
    have hi : current.val < cost.length := by omega
    apply WP.spec_bind (Slice.index_usize_spec cost current hi)
    intro inputRow hInputRow
    have hinput : inputRow = cost.val[current.val]! := by
      simpa only [getElem!_pos cost.val current.val hi] using hInputRow
    by_cases hw : inputRow.length = cost.length
    · have he : alloc.vec.Vec.len inputRow = n := by
        apply UScalar.eq_of_val_eq
        simpa only [alloc.vec.Vec.len_val,hn] using hw
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
    · have hne : alloc.vec.Vec.len inputRow ≠ n := by
        intro he
        apply hw
        simpa only [alloc.vec.Vec.len_val,hn] using congrArg UScalar.val he
      have hnotSquare : ¬ Square cost := by
        intro hsquare
        apply hw
        have hm : inputRow ∈ cost.val := by rw [hInputRow]; exact List.getElem_mem hi
        exact hsquare inputRow hm
      have hbranch : (alloc.vec.Vec.len inputRow != n) = true := bne_iff_ne.mpr hne
      simpa only [hbranch,↓reduceIte,WP.spec_ok,Bool.false_eq_true,false_iff] using hnotSquare
  · have hnot : ¬ current < n := by scalar_tac
    simp only [hnot,↓reduceIte,WP.spec_ok,eq_self,true_iff]
    apply (square_iff_index cost).mpr
    intro index hi
    exact hchecked index (by omega)

/-- Actual validation is safe on every represented matrix and returns true
exactly for the independent square-matrix predicate. -/
theorem is_square_spec (cost : Slice (alloc.vec.Vec I64)) :
    is_square cost ⦃ result => result = true ↔ Square cost ⦄ := by
  unfold is_square
  exact is_square_loop_spec cost (Slice.len cost) 0#usize (by simp) (by simp) (by simp)

end SubtreeProofs.Rust.AssignmentValidation

end
