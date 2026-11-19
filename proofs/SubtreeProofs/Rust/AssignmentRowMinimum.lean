module

public import SubtreeProofs.Rust.AssignmentInitialization
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
# Exact minimum-row initialization from actual Rust

The loop is compared with Mathlib's independent finite minimum. Empty rows
return `none`; a nonempty row returns an actual minimum-cost entry.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentRowMinimum

/-- Interpret Rust's absent minimum as the top of a finite minimum objective. -/
def toMinimum : Option I64 → WithTop ℤ
  | none => ⊤
  | some value => (value.val : WithTop ℤ)

def chooseMinimum (current : Option I64) (value : I64) : Option I64 :=
  match current with
  | none => some value
  | some old => if value < old then some value else current

theorem chooseMinimum_eq (current : Option I64) (value : I64) :
    toMinimum (chooseMinimum current value) = min (toMinimum current) (value.val : WithTop ℤ) := by
  cases current with
  | none => simp [chooseMinimum, toMinimum]
  | some old =>
    by_cases h : value < old
    · simp [chooseMinimum, toMinimum, h, ← WithTop.coe_min, min_eq_right (le_of_lt (show value.val < old.val from h))]
    · simp [chooseMinimum, toMinimum, h, ← WithTop.coe_min, min_eq_left (le_of_not_gt (show ¬ value.val < old.val from h))]

/-- The actual scan terminates, with its optional result equal to the
independently defined minimum of the whole input row. -/
theorem minimum_row_spec (row : Slice I64) : minimum_row row ⦃ result =>
    toMinimum result = (row.val.map IScalar.val).minimum ⦄ := by
  unfold minimum_row minimum_row_loop
  apply loop.spec_decr_nat (fun state => row.length - state.2.val)
    (fun state => state.2.val ≤ row.length ∧ toMinimum state.1 = ((row.val.map IScalar.val).take state.2.val).minimum)
    _ _ _ ?_ (by simp [toMinimum])
  rintro ⟨current,column⟩ ⟨hbound,hmin⟩
  dsimp only at hbound hmin ⊢
  unfold minimum_row_loop.body
  dsimp only
  split
  · rename_i hlt
    have hcol : column.val < row.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec row column hcol)
    intro value hvalue
    have hnext : toMinimum (chooseMinimum current value) = ((row.val.map IScalar.val).take (column.val + 1)).minimum := by
      have htake : (row.val.map IScalar.val).take (column.val + 1) =
          (row.val.map IScalar.val).take column.val ++ [value.val] := by
        rw [List.take_succ_eq_append_getElem (by simpa using hcol)]
        simp only [List.getElem_map, hvalue]
      rw [htake, List.minimum_concat, chooseMinimum_eq, hmin]
    cases current with
    | none =>
      simp only [bind_ok, ↓reduceIte]
      apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
      intro next hnextIndex
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      simpa [chooseMinimum, hnextIndex] using hnext
    | some old =>
      by_cases hcmp : value < old
      all_goals
        simp only [bind_ok, hcmp, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
        intro next hnextIndex
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        simpa [chooseMinimum, hcmp, hnextIndex] using hnext
  · rename_i hnot
    simp only [WP.spec_ok]
    have he : column.val = row.length := by scalar_tac
    simpa [he, ← List.map_take] using hmin

/-- On a nonempty row the result is an actual input entry and bounds every
cost from below, the property used for initial dual feasibility. -/
theorem minimum_row_nonempty_spec (row : Slice I64) (hne : row.val ≠ []) :
    minimum_row row ⦃ result => ∃ value, result = some value ∧ value ∈ row.val ∧
      ∀ other ∈ row.val, value.val ≤ other.val ⦄ := by
  apply WP.spec_mono (minimum_row_spec row)
  intro result hresult
  cases result with
  | none =>
    have hnil : row.val.map IScalar.val = [] := List.minimum_eq_top.mp hresult.symm
    exact False.elim (hne (by simpa using hnil))
  | some value =>
    have hm := List.minimum_eq_coe_iff.mp hresult.symm
    obtain ⟨actual, hactual, hval⟩ := List.mem_map.mp hm.1
    have he : actual = value := IScalar.eq_of_val_eq hval
    subst actual
    exact ⟨value, rfl, hactual, fun other ho => hm.2 other.val (List.mem_map.mpr ⟨other, ho, rfl⟩)⟩

end SubtreeProofs.Rust.AssignmentRowMinimum

end
