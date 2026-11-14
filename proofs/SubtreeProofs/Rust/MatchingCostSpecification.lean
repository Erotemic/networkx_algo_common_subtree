module

public import SubtreeProofs.Rust.Generated.VerifiedAssignmentCore
public import SubtreeProofs.Shared.AssignmentReduction
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Independent dummy cost specification for actual signed partial matching

Real left rows occupy the first index block and real right columns the
second. The independent ordered-ring dummy profit and concrete integer
cost agree under Mathlib's finite-sum indexing equivalence.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingCostSpecification

def weightValue : Option I64 → Option ℤ
  | none => none
  | some value => some value.val

def positiveProfit (weight : Option I64) : ℤ := max 0 ((weightValue weight).getD 0)

def weightsModel (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat) (row : Fin left) (col : Fin right) : Option ℤ :=
  weightValue (weights.val[row.val]!).val[col.val]!

def costAt (weights : Slice (alloc.vec.Vec (Option I64))) (left row col : Nat) : ℤ :=
  if row < left ∧ left ≤ col then -positiveProfit (weights.val[row]!).val[col-left]! else 0

/-- The actual signed negation is safe because it is applied only to a
strictly positive i64, and realizes the independent zero-clamped profit. -/
theorem negative_profit_spec (weight : Option I64) :
    matching.negative_profit weight ⦃ result => result.val = -positiveProfit weight ⦄ := by
  cases weight with
  | none => simp [matching.negative_profit,positiveProfit,weightValue]
  | some value =>
    simp only [matching.negative_profit]
    split
    · rename_i hpositive
      have hp : 0 < value.val := by scalar_tac
      apply WP.spec_mono (HNeg.hNeg.step value (by scalar_tac))
      intro result hr
      simpa only [positiveProfit,weightValue,Option.getD_some,max_eq_right (le_of_lt hp)] using hr
    · rename_i hnonpositive
      have hp : value.val ≤ 0 := by scalar_tac
      simp only [WP.spec_ok,positiveProfit,weightValue,Option.getD_some,max_eq_left hp,neg_zero,IScalar.ofInt_val_eq]

/-- Concrete array coordinates implement precisely the mathematical dummy
reduction, with no forbidden-edge sentinel or nonnegative-weight assumption. -/
theorem costAt_sum (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat)
    (row col : Fin left ⊕ Fin right) :
    costAt weights left (finSumFinEquiv row).val (finSumFinEquiv col).val =
      -WeightedMatching.AssignmentReduction.profit (weightsModel weights left right) row col := by
  cases row with
  | inl row =>
    cases col with
    | inl col =>
      have hc : ¬ left ≤ col.val := by have h := col.isLt; omega
      simp only [finSumFinEquiv_apply_left,Fin.val_castAdd,costAt,hc,and_false,↓reduceIte,
        WeightedMatching.AssignmentReduction.profit,neg_zero]
    | inr col =>
      have hr : row.val < left := row.isLt
      have hc : left ≤ left+col.val := by omega
      simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
        costAt,hr,hc,and_self,↓reduceIte,Nat.add_sub_cancel_left,positiveProfit,weightsModel,
        WeightedMatching.AssignmentReduction.profit]
  | inr row =>
    have hr : ¬ left+row.val < left := by omega
    cases col <;>
      simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
        costAt,hr,false_and,↓reduceIte,WeightedMatching.AssignmentReduction.profit,neg_zero]

end SubtreeProofs.Rust.MatchingCostSpecification

end
