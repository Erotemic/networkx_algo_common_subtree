module

public import SubtreeProofs.Shared.CopiedMatchingDuality
public import SubtreeProofs.Shared.AssignmentBiEnvelope
import Mathlib.Tactic

/-! # Two-sided numeric invariants for copied-graph initialization and deletion -/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

variable {L R K : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem initialPotential_bounds (weights : L → R → Option K) (bound : K) (hb : 0 ≤ bound)
    (hw : ∀ left right, (weights left right).getD 0 ≤ bound) (vertex : L ⊕ R) :
    0 ≤ initialPotential weights vertex ∧ initialPotential weights vertex ≤ bound := by
  cases vertex with
  | inl left => exact ⟨rowMaximum_nonnegative weights left,rowMaximum_le weights left bound hb (hw left)⟩
  | inr right => exact ⟨le_refl _,hb⟩

theorem profit_nonnegative (weights : L → R → Option K) (row column : L ⊕ R) :
    0 ≤ profit weights row column := by
  cases row <;> cases column <;> simp only [profit,AssignmentReduction.profit,add_zero,zero_add]
  all_goals first | exact le_max_left _ _ | exact le_refl _

/-- The source's larger-side initialization has the genuine two-sided
baseline, sparse feasibility and zero accumulated increment. -/
theorem initial_bi_state (weights : L → R → Option K) :
    Assignment.BiEnvelope (fun row => -initialPotential weights row) (fun column => -initialPotential weights column)
      (fun row => -initialPotential weights row) (fun column => -initialPotential weights column) 0 ∧
    Assignment.FeasibleOn (Allowed weights) (fun row column => -profit weights row column)
      (fun row => -initialPotential weights row) (fun column => -initialPotential weights column) := by
  exact ⟨Assignment.biEnvelope_initial _ _,negative_dual_feasible weights _ _ (initial_dual_feasible weights)⟩

/-- Deleting an original right vertex and its copy keeps the old feasible
potentials. Their new cumulative increment is computed from the two removed
coordinates, and obeys the smaller surviving dimension's machine budget.
No recomputed optimum or repaired assignment is a premise. -/
theorem deleted_bi_state (weights : L → R → Option K) (bound : K) (hb : 0 ≤ bound)
    (hw : ∀ left right, (weights left right).getD 0 ≤ bound)
    (rows columns : L ⊕ R → K) (increment : K)
    (henv : Assignment.BiEnvelope (fun row => -initialPotential weights row) (fun column => -initialPotential weights column)
      rows columns increment)
    (hf : Assignment.FeasibleOn (Allowed weights) (fun row column => -profit weights row column) rows columns)
    (ha : Assignment.dualValue rows columns =
      Assignment.dualValue (fun row => -initialPotential weights row) (fun column => -initialPotential weights column)+increment)
    (removed : R) :
    let V := {vertex : L ⊕ R // vertex ≠ .inr removed}
    let next := increment-(rows (.inr removed)+columns (.inr removed))
    Assignment.BiEnvelope (fun row : V => -initialPotential weights row.val) (fun column : V => -initialPotential weights column.val)
      (fun row : V => rows row.val) (fun column : V => columns column.val) next ∧
    Assignment.FeasibleOn (fun row column : V => Allowed weights row.val column.val)
      (fun row column => -profit weights row.val column.val) (fun row => rows row.val) (fun column => columns column.val) ∧
    Assignment.dualValue (fun row : V => rows row.val) (fun column : V => columns column.val) =
      Assignment.dualValue (fun row : V => -initialPotential weights row.val) (fun column : V => -initialPotential weights column.val)+next ∧
    next ≤ 2*(Fintype.card V : K)*bound := by
  dsimp only
  have hi : rows (.inr removed)+columns (.inr removed) ≤ 0 := by
    have hh := hf (.inr removed) (.inr removed) (by rfl)
    simpa only [profit,AssignmentReduction.profit,add_zero,neg_zero] using hh
  have hd := henv.delete (.inr removed) (by simp only [initialPotential,neg_zero])
    (by simp only [initialPotential,neg_zero]) hi ha
  have hf' : Assignment.FeasibleOn (fun row column : {v : L ⊕ R // v ≠ .inr removed} => Allowed weights row.val column.val)
      (fun row column => -profit weights row.val column.val) (fun row => rows row.val) (fun column => columns column.val) :=
    fun row column he => hf row.val column.val he
  refine ⟨hd.1,hf',hd.2,?_⟩
  have he : ∃ assignment : Equiv.Perm {v : L ⊕ R // v ≠ .inr removed},
      Assignment.Compatible (fun row column => Allowed weights row.val column.val) assignment := by
    refine ⟨1,?_⟩
    intro row
    change Allowed weights row.val row.val
    cases row.val <;> rfl
  have hbudget := Assignment.total_increment_bound_both_on
    (fun row : {v : L ⊕ R // v ≠ .inr removed} => -initialPotential weights row.val)
    (fun column => -initialPotential weights column.val) (fun row => rows row.val) (fun column => columns column.val)
    bound 0 (increment-(rows (.inr removed)+columns (.inr removed)))
    (fun row => neg_le_neg (initialPotential_bounds weights bound hb hw row.val).2)
    (fun column => neg_le_neg (initialPotential_bounds weights bound hb hw column.val).2)
    (fun row column _ => neg_nonpos.mpr (profit_nonnegative weights row.val column.val)) hf' he hd.2
  nlinarith

end SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

end
