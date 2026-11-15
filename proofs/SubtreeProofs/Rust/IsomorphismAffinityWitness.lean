module

public import SubtreeProofs.Rust.IsomorphismChoiceCoordinates
public import SubtreeProofs.Paper2004.AffinityIsomorphismDP
import Mathlib.Tactic

/-! # Production choice forests as independent affinity witnesses

The projection keeps both original endpoints of each input vertex. Actual
construction preserves independent level feasibility from its head/tail
invariants; actual emission reads back the same witness. The production DP
must still establish these invariants and optimum/score correspondence.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core.isomorphism_choices
open SubtreeProofs.Paper2004.AnnotatedIso

namespace SubtreeProofs.Rust.IsomorphismChoices

abbrev OriginalVertex := U32 × U32

def pairedEndpoints (ends : (U32 × U32) × (U32 × U32)) : OriginalVertex × OriginalVertex :=
  ((ends.1.1,ends.2.1),(ends.1.2,ends.2.2))

def toAffinityWitness (word : ChoiceTree) : Word (OriginalVertex × OriginalVertex) := word.map pairedEndpoints

/-- Original opening/closing positions, following the independent forest. -/
def endpointTokens : Word OriginalVertex → List U32
  | .nil => []
  | .node ends head tail => ends.1 :: (endpointTokens head ++ ends.2 :: endpointTokens tail)

theorem left_endpoint_tokens (word : ChoiceTree) :
    endpointTokens (leftProjection (toAffinityWitness word)) = (tokens word).map Prod.fst := by
  induction word with
  | nil => rfl
  | node ends head tail ihHead ihTail =>
    simp only [toAffinityWitness,leftProjection,BinaryTree.map,pairedEndpoints,endpointTokens,tokens,
      List.map_cons,List.map_append] at ihHead ihTail ⊢
    rw [ihHead,ihTail]

theorem right_endpoint_tokens (word : ChoiceTree) :
    endpointTokens (rightProjection (toAffinityWitness word)) = (tokens word).map Prod.snd := by
  induction word with
  | nil => rfl
  | node ends head tail ihHead ihTail =>
    simp only [toAffinityWitness,rightProjection,BinaryTree.map,pairedEndpoints,endpointTokens,tokens,
      List.map_cons,List.map_append] at ihHead ihTail ⊢
    rw [ihHead,ihTail]

theorem witness_affinity_score {K : Type*} [AddMonoid K] (affinity : U32 → U32 → K) (word : ChoiceTree) :
    score (fun left right : OriginalVertex => affinity left.1 right.1) (toAffinityWitness word) = affinityScore affinity word := by
  induction word with
  | nil => rfl
  | node ends head tail ihHead ihTail =>
    simp only [toAffinityWitness,BinaryTree.map,pairedEndpoints,score,affinityScore] at ihHead ihTail ⊢
    rw [ihHead,ihTail]

/-- The actual appended matched-pair forest preserves parent/identity/order
feasibility when both child forests satisfy the corresponding DP invariants. -/
theorem constructed_level_witness {K : Type*} [Zero K] [LT K] (affinity : U32 → U32 → K)
    {before : alloc.vec.Vec IsomorphismChoice} {choice : IsomorphismChoice}
    {result : Usize × alloc.vec.Vec IsomorphismChoice} (h : Constructed before choice result)
    (leftHead leftTail rightHead rightTail : Word OriginalVertex)
    (hHead : LevelWitness (fun left right : OriginalVertex => affinity left.1 right.1)
      (toAffinityWitness (optionalTree (alloc.vec.Vec.deref before) choice.head)) leftHead rightHead)
    (hTail : LevelWitness (fun left right : OriginalVertex => affinity left.1 right.1)
      (toAffinityWitness (optionalTree (alloc.vec.Vec.deref before) choice.tail)) leftTail rightTail)
    (hAffinity : 0 < affinity choice.left_open choice.right_open) :
    LevelWitness (fun left right : OriginalVertex => affinity left.1 right.1)
      (toAffinityWitness (treeAt (alloc.vec.Vec.deref result.2) result.1.val))
      (.node (choice.left_open,choice.left_close) leftHead leftTail)
      (.node (choice.right_open,choice.right_close) rightHead rightTail) := by
  rw [h.tree]
  exact level_node _ _ hHead hTail hAffinity

def WitnessReadback (witness : Word (OriginalVertex × OriginalVertex))
    (output : Option (alloc.vec.Vec U32 × alloc.vec.Vec U32)) : Prop :=
  ∃ left right, output = some (left,right) ∧
    left.val = endpointTokens (leftProjection witness) ∧ right.val = endpointTokens (rightProjection witness)

/-- Independent feasibility bounds source output size by the original input,
then the actual materializer emits precisely that original-identity witness.
The caller still owes feasibility of its selected arena forest; it is not
assumed to be optimal, and no source-success certificate is supplied. -/
theorem reconstruct_affinity_witness_spec {K : Type*} [Zero K] [LT K] (affinity : U32 → U32 → K)
    (choices : Slice IsomorphismChoice) (root : Option Usize) (hValid : ValidArena choices)
    (hRoot : ∀ index, root = some index → index.val < choices.length)
    (left right : Word OriginalVertex)
    (hWitness : AnyWitness (fun left right : OriginalVertex => affinity left.1 right.1)
      (toAffinityWitness (optionalTree choices root)) left right)
    (hInputSize : 2*min left.numNodes right.numNodes ≤ Usize.max) :
    reconstruct_isomorphism_choices choices root ⦃ output =>
      AnyWitness (fun left right : OriginalVertex => affinity left.1 right.1)
        (toAffinityWitness (optionalTree choices root)) left right ∧
      WitnessReadback (toAffinityWitness (optionalTree choices root)) output ⦄ := by
  have hCount := hWitness.numNodes_le
  simp only [toAffinityWitness,numNodes_map] at hCount
  have hSize : (tokens (optionalTree choices root)).length ≤ Usize.max := by
    rw [tokens_length]
    omega
  apply WP.spec_mono (reconstruct_isomorphism_choices_spec choices root hValid hRoot hSize)
  rintro output ⟨leftOut,rightOut,hOutput,hLeft,hRight⟩
  refine ⟨hWitness,leftOut,rightOut,hOutput,?_,?_⟩
  · exact hLeft.trans (left_endpoint_tokens _).symm
  · exact hRight.trans (right_endpoint_tokens _).symm

theorem reconstruct_level_witness_spec {K : Type*} [Zero K] [LT K] (affinity : U32 → U32 → K)
    (choices : Slice IsomorphismChoice) (root : Option Usize) (hValid : ValidArena choices)
    (hRoot : ∀ index, root = some index → index.val < choices.length)
    (left right : Word OriginalVertex)
    (hWitness : LevelWitness (fun left right : OriginalVertex => affinity left.1 right.1)
      (toAffinityWitness (optionalTree choices root)) left right)
    (hInputSize : 2*min left.numNodes right.numNodes ≤ Usize.max) :
    reconstruct_isomorphism_choices choices root ⦃ output =>
      LevelWitness (fun left right : OriginalVertex => affinity left.1 right.1)
        (toAffinityWitness (optionalTree choices root)) left right ∧
      WitnessReadback (toAffinityWitness (optionalTree choices root)) output ⦄ := by
  apply WP.spec_mono (reconstruct_affinity_witness_spec affinity choices root hValid hRoot left right hWitness.any hInputSize)
  rintro output ⟨_,hReadback⟩
  exact ⟨hWitness,hReadback⟩

end SubtreeProofs.Rust.IsomorphismChoices

end
