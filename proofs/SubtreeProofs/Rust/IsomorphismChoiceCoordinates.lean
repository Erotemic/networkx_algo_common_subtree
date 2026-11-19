module

public import SubtreeProofs.Rust.IsomorphismChoiceConstruction
import Mathlib.Tactic

/-! # Original input-coordinate bounds through construction and emission -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core.isomorphism_choices

namespace SubtreeProofs.Rust.IsomorphismChoices

def CoordinatesWithin (choice : IsomorphismChoice) (leftBound rightBound : Nat) : Prop :=
  choice.left_open.val < leftBound ∧ choice.left_close.val < leftBound ∧
    choice.right_open.val < rightBound ∧ choice.right_close.val < rightBound

def BoundedCoordinates (choices : Slice IsomorphismChoice) (leftBound rightBound : Nat) : Prop :=
  ∀ choice ∈ choices.val, CoordinatesWithin choice leftBound rightBound

theorem constructed_coordinates {before : alloc.vec.Vec IsomorphismChoice} {choice : IsomorphismChoice}
    {result : Usize × alloc.vec.Vec IsomorphismChoice} (h : Constructed before choice result)
    (leftBound rightBound : Nat) (hBefore : BoundedCoordinates (alloc.vec.Vec.deref before) leftBound rightBound)
    (hChoice : CoordinatesWithin choice leftBound rightBound) :
    BoundedCoordinates (alloc.vec.Vec.deref result.2) leftBound rightBound := by
  intro entry hm
  have hValues : (alloc.vec.Vec.deref result.2).val = (alloc.vec.Vec.deref before).val ++ [choice] := by
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using h.values
  rw [hValues] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hBefore entry hm
  · simpa only [List.mem_singleton.mp hm] using hChoice

theorem treeAt_coordinates (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (leftBound rightBound : Nat) (hCoordinates : BoundedCoordinates choices leftBound rightBound) :
    ∀ index, index < choices.length → ∀ coordinate ∈ tokens (treeAt choices index),
      coordinate.1.val < leftBound ∧ coordinate.2.val < rightBound := by
  intro index
  induction index using Nat.strong_induction_on with
  | h index ih =>
    intro hi coordinate hm
    have hEnds := hCoordinates choices.val[index] (List.getElem_mem hi)
    have hChild (child : Option Usize) (hOld : ∀ next, child = some next → next.val < index) :
        ∀ pair ∈ tokens (optionalTree choices child), pair.1.val < leftBound ∧ pair.2.val < rightBound := by
      cases child with
      | none => simp [optionalTree,tokens]
      | some next =>
        have hn := hOld next rfl
        exact ih next.val hn (by omega)
    rw [treeAt_eq choices index hValid hi] at hm
    simp only [tokens,List.mem_cons,List.mem_append] at hm
    rcases hm with rfl | (hm | rfl | hm)
    · exact ⟨hEnds.1,hEnds.2.2.1⟩
    · exact hChild _ (hValid index hi).1 coordinate hm
    · exact ⟨hEnds.2.1,hEnds.2.2.2⟩
    · exact hChild _ (hValid index hi).2 coordinate hm

theorem optionalTree_coordinates (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (leftBound rightBound : Nat) (hCoordinates : BoundedCoordinates choices leftBound rightBound)
    (root : Option Usize) (hRoot : ∀ index, root = some index → index.val < choices.length) :
    ∀ coordinate ∈ tokens (optionalTree choices root),
      coordinate.1.val < leftBound ∧ coordinate.2.val < rightBound := by
  cases root with
  | none => simp [optionalTree,tokens]
  | some index => exact treeAt_coordinates choices hValid leftBound rightBound hCoordinates index.val (hRoot index rfl)

/-- Actual emitted token indices stay within both original inputs when the
arena's endpoint coordinates do. This is a coordinate-preservation theorem,
not a parent/order/optimality theorem for arbitrary caller-built forests. -/
theorem reconstruct_coordinates_spec (choices : Slice IsomorphismChoice) (root : Option Usize)
    (hValid : ValidArena choices) (hRoot : ∀ index, root = some index → index.val < choices.length)
    (hSize : (tokens (optionalTree choices root)).length ≤ Usize.max)
    (leftBound rightBound : Nat) (hCoordinates : BoundedCoordinates choices leftBound rightBound) :
    reconstruct_isomorphism_choices choices root ⦃ output => ∃ left right,
      output = some (left,right) ∧ (∀ token ∈ left.val, token.val < leftBound) ∧
        (∀ token ∈ right.val, token.val < rightBound) ⦄ := by
  apply WP.spec_mono (reconstruct_isomorphism_choices_spec choices root hValid hRoot hSize)
  rintro output ⟨left,right,hOutput,hLeft,hRight⟩
  have hBounds := optionalTree_coordinates choices hValid leftBound rightBound hCoordinates root hRoot
  refine ⟨left,right,hOutput,?_,?_⟩
  · intro token hm
    rw [hLeft] at hm
    obtain ⟨coordinate,hMember,rfl⟩ := List.mem_map.mp hm
    exact (hBounds coordinate hMember).1
  · intro token hm
    rw [hRight] at hm
    obtain ⟨coordinate,hMember,rfl⟩ := List.mem_map.mp hm
    exact (hBounds coordinate hMember).2

end SubtreeProofs.Rust.IsomorphismChoices

end
