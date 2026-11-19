module

public import SubtreeProofs.Rust.MatchingMatrixRepresentation
public import SubtreeProofs.Rust.MatchingDecodedWitness
public import SubtreeProofs.Shared.AssignmentReindex
import Mathlib.Tactic

/-!
# Concrete indexed witness and optimum bridge for actual partial matching

The source matrix and decoded coordinate list use the same left/right finite
sum convention as the independent matching reduction. Actual assignment
correctness therefore gives a maximum matching and exact negated-cost weight.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.MatchingAssignmentBridge

open MatchingCostSpecification MatchingCostConstruction MatchingMatrixRepresentation MatchingDecoding MatchingDecodedWitness

/-- Standard left/right sum indexing, with only the checked dimension cast. -/
def sumIndices {left right count : Nat} (h : count = left+right) : (Fin left ⊕ Fin right) ≃ Fin count :=
  finSumFinEquiv.trans (finCongr h.symm)

@[simp] theorem sumIndices_val {left right count : Nat} (h : count = left+right) (index : Fin left ⊕ Fin right) :
    (sumIndices h index).val = (finSumFinEquiv index).val := rfl

@[simp] theorem sumIndices_left_val {left right count : Nat} (h : count = left+right) (index : Fin left) :
    (sumIndices h (.inl index)).val = index.val := rfl

@[simp] theorem sumIndices_right_val {left right count : Nat} (h : count = left+right) (index : Fin right) :
    (sumIndices h (.inr index)).val = left+index.val := rfl

/-- Every physical source matrix cell is the independent dummy cost under
Mathlib's sum indexing, including all real/dummy coordinate combinations. -/
theorem built_cost_reindex (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension n : Usize)
    (dims : Dimensions weights left right dimension) (cost : alloc.vec.Vec (alloc.vec.Vec I64))
    (hbuilt : Built weights left dimension cost) (hn : n.val = dimension.val) (row col : Fin left.val ⊕ Fin right.val) :
    AssignmentReconstruction.matrix (alloc.vec.Vec.deref cost) n
      (sumIndices (hn.trans dims.dimension_eq) row) (sumIndices (hn.trans dims.dimension_eq) col) =
        -WeightedMatching.AssignmentReduction.profit (weightsModel weights left.val right.val) row col := by
  let indices := sumIndices (hn.trans dims.dimension_eq)
  have hr : (indices row).val < dimension.val := by rw [← hn]; exact (indices row).isLt
  have hc : (indices col).val < dimension.val := by rw [← hn]; exact (indices col).isLt
  simp only [AssignmentReconstruction.matrix,alloc.vec.Vec.deref,Slice.from_val]
  rw [built_cell weights left dimension cost hbuilt _ _ hr hc]
  simpa only [indices,sumIndices_val] using costAt_sum weights left.val right.val row col

/-- The actual decoded assignment coordinate is exactly the mathematical
real-real permutation edge after index transport. -/
theorem column_assignment_iff (left right n : Nat) (hn : n = left+right) (assignment : Equiv.Perm (Fin n))
    (columns : alloc.vec.Vec Usize) (hdecoded : columns.length = n ∧
      ∀ row : Fin n, columns.val[row.val]!.val = (assignment row).val) (row : Fin left) (col : Fin right) :
    columns.val[row.val]!.val = left+col.val ↔
      ((sumIndices hn).permCongr.symm assignment) (.inl row) = .inr col := by
  let indices := sumIndices hn
  let transferred := indices.permCongr.symm assignment
  have happly : indices (transferred (.inl row)) = assignment (indices (.inl row)) := by
    simp only [transferred,Equiv.permCongr_symm_apply,Equiv.apply_symm_apply]
  have hd := hdecoded.2 (indices (.inl row))
  simp only [indices,sumIndices_left_val] at hd
  rw [hd]
  constructor
  · intro he
    apply indices.injective
    rw [happly]
    apply Fin.ext
    simpa only [indices,sumIndices_right_val] using he
  · intro he
    have hh := congrArg indices he
    rw [happly] at hh
    simpa only [indices,sumIndices_right_val] using congrArg Fin.val hh

/-- The actual decoder's natural-coordinate list represents exactly the
independent finite matching, with every index retained on both input sides. -/
theorem mem_prefix_iff_decode (weights : Slice (alloc.vec.Vec (Option I64))) (left right n : Usize)
    (hn : n.val = left.val+right.val) (assignment : Equiv.Perm (Fin n.val)) (columns : alloc.vec.Vec Usize)
    (hdecoded : AssignmentReconstruction.Decoded n assignment columns) (pair : Nat × Nat) :
    pair ∈ decodedPrefix weights left.val right.val (alloc.vec.Vec.deref columns) left.val ↔
      ∃ concrete : Fin left.val × Fin right.val,
        concrete ∈ WeightedMatching.AssignmentReduction.decode (weightsModel weights left.val right.val) ((sumIndices hn).permCongr.symm assignment) ∧
          (concrete.1.val,concrete.2.val) = pair := by
  rw [mem_decodedPrefix]
  simp only [alloc.vec.Vec.deref,Slice.from_val]
  constructor
  · rintro ⟨hl,hr,hcolumn,hpositive⟩
    let row : Fin left.val := ⟨pair.1,hl⟩
    let col : Fin right.val := ⟨pair.2,hr⟩
    refine ⟨(row,col),?_,rfl⟩
    apply (WeightedMatching.AssignmentReduction.mem_decode _ _ _).mpr
    refine ⟨?_,?_⟩
    · exact (column_assignment_iff left.val right.val n.val hn assignment columns hdecoded row col).mp hcolumn
    · exact hpositive
  · rintro ⟨⟨row,col⟩,hmatching,rfl⟩
    have hm := (WeightedMatching.AssignmentReduction.mem_decode _ _ _).mp hmatching
    refine ⟨row.isLt,col.isLt,?_,?_⟩
    · exact (column_assignment_iff left.val right.val n.val hn assignment columns hdecoded row col).mpr hm.1
    · exact hm.2

/-- Correct actual assignment output on the constructed matrix gives the
independent maximum partial matching and exact negated machine cost. -/
theorem assignment_maximum (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension n : Usize)
    (dims : Dimensions weights left right dimension) (cost : alloc.vec.Vec (alloc.vec.Vec I64))
    (hbuilt : Built weights left dimension cost) (hn : n.val = dimension.val) (result : verified_assignment_core.Assignment)
    (hcorrect : AssignmentReturnedSpecification.Correct (alloc.vec.Vec.deref cost) n result) :
    ∃ assignment : Equiv.Perm (Fin n.val), AssignmentReconstruction.Decoded n assignment result.column_for_row ∧
      WeightedMatching.IsMaximum (weightsModel weights left.val right.val)
        (WeightedMatching.AssignmentReduction.decode (weightsModel weights left.val right.val) ((sumIndices (hn.trans dims.dimension_eq)).permCongr.symm assignment)) ∧
      WeightedMatching.weight (weightsModel weights left.val right.val)
        (WeightedMatching.AssignmentReduction.decode (weightsModel weights left.val right.val) ((sumIndices (hn.trans dims.dimension_eq)).permCongr.symm assignment)) = -result.cost.val := by
  obtain ⟨assignment,hdecoded,_,_,hfeasible,htight,hcost,_,_⟩ := hcorrect
  have h := Assignment.reindexed_assignment_decodes (weightsModel weights left.val right.val) (sumIndices (hn.trans dims.dimension_eq))
    (AssignmentReconstruction.matrix (alloc.vec.Vec.deref cost) n)
    (AssignmentReturnedSpecification.exportedPotential result.row_potential n)
    (AssignmentReturnedSpecification.exportedPotential result.column_potential n) assignment
    (built_cost_reindex weights left right dimension n dims cost hbuilt hn) hfeasible htight
  exact ⟨assignment,hdecoded,h.1,by rw [hcost]; exact h.2⟩

end SubtreeProofs.Rust.MatchingAssignmentBridge

end
