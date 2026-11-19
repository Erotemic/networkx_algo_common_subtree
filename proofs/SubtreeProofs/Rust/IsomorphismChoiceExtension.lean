module

public import SubtreeProofs.Rust.IsomorphismChoiceEntrypoint
import Mathlib.Tactic

/-! # Arena extension preserves production isomorphism witnesses

Memoized choices retain their original meaning when later matched-pair choices
are appended. This is a forest/index property, independent of weighted score
comparisons and of the imperative witness-emission loop.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core.isomorphism_choices

namespace SubtreeProofs.Rust.IsomorphismChoices

/-- Every old indexed forest is invariant under arbitrary suffix extension,
including arenas whose unreachable records are invalid. -/
theorem treeAt_prefix (before after : Slice IsomorphismChoice) (hPrefix : before.val <+: after.val) :
    ∀ index, index < before.length → treeAt after index = treeAt before index := by
  intro index
  induction index using Nat.strong_induction_on with
  | h index ih =>
    intro hi
    have hLength : before.length ≤ after.length := hPrefix.length_le
    have ha : index < after.length := by omega
    have hCell : after.val[index] = before.val[index] := (hPrefix.getElem hi).symm
    conv_lhs => rw [treeAt]
    conv_rhs => rw [treeAt]
    simp only [dite_eq_left hi,dite_eq_left ha,hCell]
    congr 1
    · cases hh : before.val[index].head with
      | none => rfl
      | some child =>
        by_cases hc : child.val < index
        · simp only [hc,↓reduceIte]
          exact ih child.val hc (by omega)
        · simp only [hc,↓reduceIte]
    · cases ht : before.val[index].tail with
      | none => rfl
      | some child =>
        by_cases hc : child.val < index
        · simp only [hc,↓reduceIte]
          exact ih child.val hc (by omega)
        · simp only [hc,↓reduceIte]

theorem optionalTree_prefix (before after : Slice IsomorphismChoice) (hPrefix : before.val <+: after.val)
    (root : Option Usize) (hRoot : ∀ index, root = some index → index.val < before.length) :
    optionalTree after root = optionalTree before root := by
  cases root with
  | none => rfl
  | some index => exact treeAt_prefix before after hPrefix index.val (hRoot index rfl)

theorem appended_length (before after : Slice IsomorphismChoice) (choice : IsomorphismChoice)
    (hAppend : after.val = before.val ++ [choice]) : after.length = before.length+1 := by
  have h := congrArg List.length hAppend
  simpa only [List.length_append,List.length_singleton,Slice.length] using h

theorem appended_cell (before after : Slice IsomorphismChoice) (choice : IsomorphismChoice)
    (hAppend : after.val = before.val ++ [choice]) :
    after.val[before.length]'(by
      change before.length < after.length
      rw [appended_length before after choice hAppend]
      omega) = choice := by
  simp only [hAppend,Slice.length,List.getElem_append_right (le_refl before.val.length),
    Nat.sub_self,List.getElem_cons_zero]

/-- Appending references to old choices preserves all backward links and makes
the returned old-length coordinate a valid new root. -/
theorem validArena_append (before after : Slice IsomorphismChoice) (choice : IsomorphismChoice)
    (hAppend : after.val = before.val ++ [choice]) (hValid : ValidArena before)
    (hHead : ∀ child, choice.head = some child → child.val < before.length)
    (hTail : ∀ child, choice.tail = some child → child.val < before.length) :
    ValidArena after := by
  have hLength := appended_length before after choice hAppend
  have hPrefix : before.val <+: after.val := by rw [hAppend]; exact List.prefix_append _ _
  intro index hi
  by_cases hOld : index < before.length
  · have hCell : after.val[index] = before.val[index] := (hPrefix.getElem hOld).symm
    rw [hCell]
    exact hValid index hOld
  · have he : index = before.length := by omega
    subst index
    rw [appended_cell before after choice hAppend]
    exact ⟨hHead,hTail⟩

/-- The new root's independent forest consists exactly of its original token
pair, the two old child forests and no other arena entries. -/
theorem appended_tree (before after : Slice IsomorphismChoice) (choice : IsomorphismChoice)
    (hAppend : after.val = before.val ++ [choice]) (hValid : ValidArena before)
    (hHead : ∀ child, choice.head = some child → child.val < before.length)
    (hTail : ∀ child, choice.tail = some child → child.val < before.length) :
    treeAt after before.length =
      .node ((choice.left_open,choice.right_open),(choice.left_close,choice.right_close))
        (optionalTree before choice.head) (optionalTree before choice.tail) := by
  have hNew := validArena_append before after choice hAppend hValid hHead hTail
  have hLength := appended_length before after choice hAppend
  have hPrefix : before.val <+: after.val := by rw [hAppend]; exact List.prefix_append _ _
  rw [treeAt_eq after before.length hNew (by omega),appended_cell before after choice hAppend,
    optionalTree_prefix before after hPrefix choice.head hHead,
    optionalTree_prefix before after hPrefix choice.tail hTail]

end SubtreeProofs.Rust.IsomorphismChoices

end
