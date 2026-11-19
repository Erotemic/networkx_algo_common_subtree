module

public import SubtreeProofs.Rust.Generated.VerifiedAssignmentCore
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-! # Actual optional sparse cut selection and matrix shape validation -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

/-- Absence is the top of the independent minimum-slack objective. -/
def toMinimum : Option sparse.SparseCut → WithTop ℤ
  | none => ⊤
  | some cut => (cut.delta.val : WithTop ℤ)

/-- The actual selector attains the independent two-way minimum and preserves
one of the exact input records, including its original row/column identity. -/
theorem select_cut_spec (previous : Option sparse.SparseCut) (candidate : sparse.SparseCut) :
    sparse.select_cut previous candidate ⦃ result =>
      toMinimum (some result) = min (toMinimum previous) (candidate.delta.val : WithTop ℤ) ∧
      (some result = previous ∨ result = candidate) ⦄ := by
  cases previous with
  | none =>
    rw [sparse.select_cut]
    simp only [WP.spec_ok,toMinimum,min_top_left,or_true]
    exact ⟨True.intro,True.intro⟩
  | some old =>
    by_cases h : candidate.delta < old.delta
    · rw [sparse.select_cut]
      simp only [h,↓reduceIte,WP.spec_ok,toMinimum,← WithTop.coe_min]
      rw [min_eq_right (le_of_lt (show candidate.delta.val < old.delta.val from h))]
      exact ⟨rfl,Or.inr True.intro⟩
    · rw [sparse.select_cut]
      simp only [h,↓reduceIte,WP.spec_ok,toMinimum,← WithTop.coe_min]
      rw [min_eq_left (le_of_not_gt (show ¬ candidate.delta.val < old.delta.val from h))]
      exact ⟨rfl,Or.inl True.intro⟩

/-- The independent square-shape predicate reads every actual original row. -/
def Square (cost : Slice (alloc.vec.Vec (Option I64))) : Prop :=
  ∀ index, index < cost.length → (cost.val[index]!).length = cost.length

/-- The actual source shape loop safely terminates and exactly decides the
input shape on every represented optional-cost matrix. -/
theorem square_shape_spec (cost : Slice (alloc.vec.Vec (Option I64))) :
    sparse.square_shape cost ⦃ result => result = true ↔ Square cost ⦄ := by
  unfold sparse.square_shape sparse.square_shape_loop
  apply loop.spec_decr_nat (fun row => cost.length-row.val)
    (fun row => row.val ≤ cost.length ∧ ∀ index, index < row.val → (cost.val[index]!).length = cost.length)
    _ _ _ ?_ (by simp)
  intro row hInv
  obtain ⟨hbound,hSeen⟩ := hInv
  unfold sparse.square_shape_loop.body
  dsimp only
  have hlen := Slice.len_val cost
  split
  · rename_i hlt
    have hr : row.val < cost.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec cost row hr)
    intro value hValue
    have hv : (cost.val[row.val]!).length = value.length := by
      rw [getElem!_pos cost.val row.val hr,← hValue]
    have hvlen := alloc.vec.Vec.len_val value
    split
    · rename_i hbad
      simp only [WP.spec_ok,Bool.false_eq_true,false_iff]
      intro hSquare
      have he := hv.symm.trans (hSquare row.val hr)
      have heMachine : alloc.vec.Vec.len value = Slice.len cost := by scalar_tac
      simp only [heMachine,bne_self_eq_false,Bool.false_eq_true] at hbad
    · rename_i hgood
      have heMachine : alloc.vec.Vec.len value = Slice.len cost := by
        by_contra hn
        exact hgood (bne_iff_ne.mpr hn)
      have he : value.length = cost.length := by scalar_tac
      apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
      intro next hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
      intro index hi
      by_cases hh : index < row.val
      · exact hSeen index hh
      · have hiEq : index = row.val := by scalar_tac
        rw [hiEq,hv,he]
  · rename_i hnot
    simp only [WP.spec_ok,true_iff]
    have he : row.val = cost.length := by scalar_tac
    intro index hi
    exact hSeen index (by omega)

end SubtreeProofs.Rust.SparseCut

end
