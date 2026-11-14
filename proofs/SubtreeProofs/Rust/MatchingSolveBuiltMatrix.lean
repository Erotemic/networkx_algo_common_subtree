module

public import SubtreeProofs.Rust.MatchingAssignmentBridge
import Mathlib.Tactic

/-!
# Actual assignment-backed partial-matching solve and indexed optimum

The actual verified assignment API consumes the built dummy matrix. Actual
pair decoding and safe negation of its cost return an indexed list representing
an independently maximum compatible partial matching, with exactly its weight.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingSolveBuiltMatrix

open MatchingCostSpecification MatchingCostConstruction MatchingMatrixRepresentation MatchingDecoding MatchingDecodedWitness
open AssignmentColumnScan MatchingAssignmentBridge AssignmentEntrypoint AssignmentReturnedSpecification AssignmentNumericBounds

/-- Exact returned indices, list uniqueness, independent feasibility/global
optimality, and exact weight of the actual partial-matching result. -/
def CorrectFor (left right : Usize) (weights : Fin left.val → Fin right.val → Option ℤ)
    (result : matching.PartialMatching) : Prop :=
  ∃ pairs : Finset (Fin left.val × Fin right.val), (result.pairs.val.map pairValue).Nodup ∧
    (∀ pair : Nat × Nat, pair ∈ result.pairs.val.map pairValue ↔
      ∃ concrete ∈ pairs, (concrete.1.val,concrete.2.val) = pair) ∧
    WeightedMatching.IsMaximum weights pairs ∧ result.weight.val = WeightedMatching.weight weights pairs

/-- Specialization of the indexed independent optimum contract to a concrete
optional-weight input matrix. -/
def CorrectPartial (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Usize) (result : matching.PartialMatching) : Prop :=
  CorrectFor left right (weightsModel weights left.val right.val) result

/-- Every integer assignment total is bounded by the number of original
signed i64 entries in that assignment, independently of optimality. -/
theorem assignment_cost_bounds (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (assignment : Equiv.Perm (Fin n.val)) :
    -((n.val : ℤ)*costMagnitude) ≤ Assignment.cost (AssignmentReconstruction.matrix cost n) assignment ∧
      Assignment.cost (AssignmentReconstruction.matrix cost n) assignment ≤ (n.val : ℤ)*costMagnitude := by
  constructor
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n.val))) (fun row _ => (cost_bounds cost n row (assignment row)).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_neg,Assignment.cost] using h
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n.val))) (fun row _ => (cost_bounds cost n row (assignment row)).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Assignment.cost] using h

theorem negate_cost_fits (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (result : verified_assignment_core.Assignment)
    (hn : n.val ≤ U32.max) (hcorrect : Correct cost n result) : Fits128 (-result.cost.val) := by
  obtain ⟨assignment,_,_,_,_,_,he,_,_⟩ := hcorrect
  have hb := assignment_cost_bounds cost n assignment
  rw [← he] at hb
  have hm : 0 ≤ costMagnitude := by norm_num [costMagnitude]
  have hp : 0 ≤ (n.val : ℤ)*costMagnitude := mul_nonneg (Nat.cast_nonneg _) hm
  apply fits128_of_bound n.val _ hn
  · unfold reducedBound cumulativeBound
    linarith
  · unfold reducedBound cumulativeBound
    linarith

/-- Actual assignment, decoding and cost negation safely return a complete
indexed maximum partial-matching witness. Local arithmetic ranges and
assignment/path/optimum certificates are not supplied by the caller. -/
theorem solve_built_matrix_spec (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension : Usize)
    (dims : Dimensions weights left right dimension) (cost : alloc.vec.Vec (alloc.vec.Vec I64))
    (hbuilt : Built weights left dimension cost) (hn : dimension.val ≤ U32.max) (hextent : dimension.val < Usize.max) :
    matching.solve_built_matrix weights left right (alloc.vec.Vec.deref cost) ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧ CorrectPartial weights left right result ⦄ := by
  unfold matching.solve_built_matrix
  apply WP.spec_bind (min_cost_assignment_spec (alloc.vec.Vec.deref cost) (built_admissible weights left dimension cost hbuilt hn hextent))
  rintro assignmentOutput ⟨assignment,hAssignmentOutput,hcorrect⟩
  subst assignmentOutput
  let n := Slice.len (alloc.vec.Vec.deref cost)
  have hdim : n.val = dimension.val := by
    simpa only [n,Slice.len_val,alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using built_length weights left dimension cost hbuilt
  obtain ⟨permutation,hdecoded,hmaximum,hweight⟩ := assignment_maximum weights left right dimension n dims cost hbuilt hdim assignment hcorrect
  have hcolumns : left.val ≤ (alloc.vec.Vec.deref assignment.column_for_row).length := by
    have hb : left.val ≤ assignment.column_for_row.length := by
      rw [hdecoded.1,hdim,dims.dimension_eq]
      omega
    simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using hb
  apply WP.spec_bind (decode_pairs_spec weights left right dimension (alloc.vec.Vec.deref assignment.column_for_row) dims hcolumns)
  intro pairs hPairs
  have hfit := negate_cost_fits (alloc.vec.Vec.deref cost) n assignment (by rw [hdim]; exact hn) hcorrect
  apply WP.spec_bind (AssignmentArithmetic.checked_sub_spec 0#i128 assignment.cost (by simpa using hfit.1) (by simpa using hfit.2))
  rintro weightOption ⟨weight,hWeightOption,hWeight⟩
  subst weightOption
  simp only [WP.spec_ok]
  refine ⟨({ pairs := pairs, weight := weight } : matching.PartialMatching),rfl,
    WeightedMatching.AssignmentReduction.decode (weightsModel weights left.val right.val) ((sumIndices (hdim.trans dims.dimension_eq)).permCongr.symm permutation),
    ?_,?_,?_,?_⟩
  · change (pairs.val.map pairValue).Nodup
    rw [hPairs]
    exact decodedPrefix_nodup weights left.val right.val (alloc.vec.Vec.deref assignment.column_for_row) left.val
  · intro pair
    change pair ∈ pairs.val.map pairValue ↔ _
    rw [hPairs]
    exact mem_prefix_iff_decode weights left right n (hdim.trans dims.dimension_eq) permutation assignment.column_for_row hdecoded pair
  · exact hmaximum
  · change weight.val = _
    have hw : weight.val = -assignment.cost.val := by simpa using hWeight
    exact hw.trans hweight.symm

end SubtreeProofs.Rust.MatchingSolveBuiltMatrix

end
