module

public import SubtreeProofs.Rust.MatchingValidation
public import SubtreeProofs.Rust.MatchingSolveBuiltMatrix
import Mathlib.Tactic

/-! # Actual no-positive-edge early return for exact partial matching

The scans decide an independent entrywise sign predicate. Every feasible
partial matching then has nonpositive weight, so the empty output is maximum.
This bypasses the square dummy matrix without changing accepted inputs.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingNonpositive

open MatchingCostSpecification MatchingValidation MatchingSolveBuiltMatrix

def RowNonpositive (row : Slice (Option I64)) : Prop :=
  ∀ column < row.length, (weightValue row.val[column]!).getD 0 ≤ 0

def Nonpositive (weights : Slice (alloc.vec.Vec (Option I64))) : Prop :=
  ∀ row < weights.length, RowNonpositive (alloc.vec.Vec.deref weights.val[row]!)

theorem row_has_positive_loop_spec (row : Slice (Option I64)) (column : Usize)
    (hcolumn : column.val ≤ row.length)
    (hprefix : ∀ index < column.val, (weightValue row.val[index]!).getD 0 ≤ 0) :
    matching.row_has_positive_loop row column ⦃ result => result = false ↔ RowNonpositive row ⦄ := by
  unfold matching.row_has_positive_loop
  apply loop.spec_decr_nat (fun current => row.length-current.val)
    (fun current => current.val ≤ row.length ∧
      ∀ index < current.val, (weightValue row.val[index]!).getD 0 ≤ 0)
    (fun result => result = false ↔ RowNonpositive row) _ column ?_ ⟨hcolumn,hprefix⟩
  intro current hinv
  rcases hinv with ⟨hbound,hchecked⟩
  have hn := Slice.len_val row
  unfold matching.row_has_positive_loop.body
  dsimp only
  split
  · rename_i hr
    have hi : current.val < row.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec row current hi)
    intro entry hEntry
    have hentry : entry = row.val[current.val]! := by
      simpa only [getElem!_pos row.val current.val hi] using hEntry
    have hcontinue (hhere : (weightValue entry).getD 0 ≤ 0) :
        (do let next ← current+1#usize; ok (cont next)) ⦃ result => match result with
          | .done result => result = false ↔ RowNonpositive row
          | .cont next => (next.val ≤ row.length ∧
              ∀ index < next.val, (weightValue row.val[index]!).getD 0 ≤ 0) ∧
                row.length-next.val < row.length-current.val ⦄ := by
      apply WP.spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
      intro next hNext
      have hnext : next.val = current.val+1 := by simpa using hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by omega,?_⟩,by omega⟩
      intro index hb
      by_cases he : index = current.val
      · subst index
        simpa only [hentry] using hhere
      · exact hchecked index (by omega)
    cases entry with
    | none =>
      simp only
      apply WP.spec_mono (hcontinue (by simp [weightValue]))
      intro result h
      cases result <;> exact h
    | some value =>
      simp only
      split
      · rename_i hp
        have hpos : 0 < value.val := by scalar_tac
        simp only [WP.spec_ok,Bool.true_eq_false,false_iff]
        intro hall
        have hh := hall current.val hi
        rw [← hentry] at hh
        simp only [weightValue,Option.getD_some] at hh
        omega
      · rename_i hp
        have hn : (weightValue (some value)).getD 0 ≤ 0 := by
          simp only [weightValue,Option.getD_some]
          scalar_tac
        apply WP.spec_mono (hcontinue hn)
        intro result h
        cases result <;> exact h
  · rename_i hr
    simp only [WP.spec_ok,eq_self,true_iff]
    intro index hi
    exact hchecked index (by scalar_tac)

theorem row_has_positive_spec (row : Slice (Option I64)) :
    matching.row_has_positive row ⦃ result => result = false ↔ RowNonpositive row ⦄ := by
  exact row_has_positive_loop_spec row 0#usize (by simp) (by simp)

theorem has_positive_loop_spec (weights : Slice (alloc.vec.Vec (Option I64))) (row : Usize)
    (hrow : row.val ≤ weights.length)
    (hprefix : ∀ index < row.val, RowNonpositive (alloc.vec.Vec.deref weights.val[index]!)) :
    matching.has_positive_loop weights row ⦃ result => result = false ↔ Nonpositive weights ⦄ := by
  unfold matching.has_positive_loop
  apply loop.spec_decr_nat (fun current => weights.length-current.val)
    (fun current => current.val ≤ weights.length ∧
      ∀ index < current.val, RowNonpositive (alloc.vec.Vec.deref weights.val[index]!))
    (fun result => result = false ↔ Nonpositive weights) _ row ?_ ⟨hrow,hprefix⟩
  intro current hinv
  rcases hinv with ⟨hbound,hchecked⟩
  have hn := Slice.len_val weights
  unfold matching.has_positive_loop.body
  dsimp only
  split
  · rename_i hr
    have hi : current.val < weights.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec weights current hi)
    intro inputRow hInputRow
    have hinput : inputRow = weights.val[current.val]! := by
      simpa only [getElem!_pos weights.val current.val hi] using hInputRow
    apply WP.spec_bind (row_has_positive_spec (alloc.vec.Vec.deref inputRow))
    intro positive hPositive
    cases positive with
    | true =>
      simp only [Bool.true_eq_false,false_iff] at hPositive
      simp only [↓reduceIte,WP.spec_ok,Bool.true_eq_false,false_iff]
      intro hall
      exact hPositive (by rw [hinput]; exact hall current.val hi)
    | false =>
      have hhere : RowNonpositive (alloc.vec.Vec.deref inputRow) := hPositive.mp rfl
      simp only [Bool.false_eq_true,↓reduceIte]
      apply WP.spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
      intro next hNext
      have hnext : next.val = current.val+1 := by simpa using hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by omega,?_⟩,by omega⟩
      intro index hb
      by_cases he : index = current.val
      · subst index
        simpa only [hinput] using hhere
      · exact hchecked index (by omega)
  · rename_i hr
    simp only [WP.spec_ok,eq_self,true_iff]
    intro index hi
    exact hchecked index (by scalar_tac)

theorem has_positive_spec (weights : Slice (alloc.vec.Vec (Option I64))) :
    matching.has_positive weights ⦃ result => result = false ↔ Nonpositive weights ⦄ := by
  exact has_positive_loop_spec weights 0#usize (by simp) (by simp)

/-- Every independently feasible competitor has weight at most zero. The
original-index and uniqueness clauses hold for the actual empty vector. -/
theorem empty_correct (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Usize)
    (hleft : left.val = weights.length) (hshape : Rectangular weights right.val)
    (hnonpositive : Nonpositive weights) :
    CorrectPartial weights left right { pairs := alloc.vec.Vec.new _, weight := 0#i128 } := by
  refine ⟨∅,?_,?_,?_,?_⟩
  · simp [alloc.vec.Vec.new]
  · intro pair
    simp [alloc.vec.Vec.new]
  · refine ⟨WeightedMatching.valid_empty _,?_⟩
    intro pairs _
    rw [WeightedMatching.weight_empty]
    apply Finset.sum_nonpos
    intro pair _
    have hr : pair.1.val < weights.length := by rw [← hleft]; exact pair.1.isLt
    have hrow := (rectangular_iff_index weights right.val).mp hshape pair.1.val hr
    have hc : pair.2.val < (alloc.vec.Vec.deref weights.val[pair.1.val]!).length := by
      have hlen : (alloc.vec.Vec.deref weights.val[pair.1.val]!).length = right.val := by
        simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using hrow
      rw [hlen]
      exact pair.2.isLt
    simpa only [weightsModel,alloc.vec.Vec.deref,Slice.from_val] using
      hnonpositive pair.1.val hr pair.2.val hc
  · simp [WeightedMatching.weight_empty]

end SubtreeProofs.Rust.MatchingNonpositive

end
