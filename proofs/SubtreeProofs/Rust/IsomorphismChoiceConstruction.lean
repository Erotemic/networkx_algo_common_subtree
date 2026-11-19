module

public import SubtreeProofs.Rust.IsomorphismChoiceExtension
import Mathlib.Tactic

/-! # Actual production matched-pair construction and materialization

The optimized weighted solver calls the actual integer-only append helper.
Its old memo references remain meaningful and its new reference denotes the
independently assembled forest. Arithmetic scores are interpreted separately;
no floating-point operations are identified with an abstract additive model.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core.isomorphism_choices

namespace SubtreeProofs.Rust.IsomorphismChoices

def matchedTree (before : Slice IsomorphismChoice) (choice : IsomorphismChoice) : ChoiceTree :=
  .node ((choice.left_open,choice.right_open),(choice.left_close,choice.right_close))
    (optionalTree before choice.head) (optionalTree before choice.tail)

structure Constructed (before : alloc.vec.Vec IsomorphismChoice) (choice : IsomorphismChoice)
    (result : Usize × alloc.vec.Vec IsomorphismChoice) : Prop where
  index : result.1.val = before.length
  values : result.2.val = before.val ++ [choice]
  length : result.2.length = before.length+1
  valid : ValidArena (alloc.vec.Vec.deref result.2)
  root : result.1.val < (alloc.vec.Vec.deref result.2).length
  stable : ∀ index, index < before.length →
    treeAt (alloc.vec.Vec.deref result.2) index = treeAt (alloc.vec.Vec.deref before) index
  tree : treeAt (alloc.vec.Vec.deref result.2) result.1.val = matchedTree (alloc.vec.Vec.deref before) choice

theorem empty_arena_valid : ValidArena (alloc.vec.Vec.deref (alloc.vec.Vec.new IsomorphismChoice)) := by
  intro index hi
  simp [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.new] at hi

/-- The actual production append preserves the old arena, validates every
old memo reference and assembles precisely the intended new forest. The only
size assumption is space for one source vector entry. -/
theorem append_isomorphism_choice_spec (before : alloc.vec.Vec IsomorphismChoice) (choice : IsomorphismChoice)
    (hRoom : before.length < Usize.max) (hValid : ValidArena (alloc.vec.Vec.deref before))
    (hHead : ∀ child, choice.head = some child → child.val < before.length)
    (hTail : ∀ child, choice.tail = some child → child.val < before.length) :
    append_isomorphism_choice before choice ⦃ result => Constructed before choice result ⦄ := by
  unfold append_isomorphism_choice
  apply WP.spec_bind (alloc.vec.Vec.push_spec before choice hRoom)
  intro after hAppend
  have hOldLength : (alloc.vec.Vec.deref before).length = before.length := by
    simp [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length]
  have hNewLength : (alloc.vec.Vec.deref after).length = after.length := by
    simp [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length]
  have hAppendView : (alloc.vec.Vec.deref after).val = (alloc.vec.Vec.deref before).val ++ [choice] := by
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using hAppend
  have hHead' : ∀ child, choice.head = some child → child.val < (alloc.vec.Vec.deref before).length := by
    simpa only [hOldLength] using hHead
  have hTail' : ∀ child, choice.tail = some child → child.val < (alloc.vec.Vec.deref before).length := by
    simpa only [hOldLength] using hTail
  have hPrefix : (alloc.vec.Vec.deref before).val <+: (alloc.vec.Vec.deref after).val := by
    rw [hAppendView]
    exact List.prefix_append _ _
  have hLength : after.length = before.length+1 := by
    simpa only [hOldLength,hNewLength] using appended_length _ _ choice hAppendView
  simp only [WP.spec_ok]
  refine ⟨alloc.vec.Vec.len_val before,hAppend,hLength,
    validArena_append _ _ choice hAppendView hValid hHead' hTail',?_,?_,?_⟩
  · simp only [alloc.vec.Vec.len_val,hNewLength,hLength]
    omega
  · intro index hi
    exact treeAt_prefix _ _ hPrefix index (by rw [hOldLength]; exact hi)
  · simpa only [alloc.vec.Vec.len_val,hOldLength,matchedTree] using
      appended_tree _ _ choice hAppendView hValid hHead' hTail'

/-- Compose actual construction and actual emission, deriving new-root validity
and its interpretation instead of supplying an output/arena certificate. -/
theorem append_and_reconstruct_spec (before : alloc.vec.Vec IsomorphismChoice) (choice : IsomorphismChoice)
    (hRoom : before.length < Usize.max) (hValid : ValidArena (alloc.vec.Vec.deref before))
    (hHead : ∀ child, choice.head = some child → child.val < before.length)
    (hTail : ∀ child, choice.tail = some child → child.val < before.length)
    (hSize : (tokens (matchedTree (alloc.vec.Vec.deref before) choice)).length ≤ Usize.max) :
    (do
      let (index,after) ← append_isomorphism_choice before choice
      reconstruct_isomorphism_choices (alloc.vec.Vec.deref after) (some index)) ⦃ output =>
        EmissionPost ((tokens (matchedTree (alloc.vec.Vec.deref before) choice)).map Prod.fst)
          ((tokens (matchedTree (alloc.vec.Vec.deref before) choice)).map Prod.snd) output ⦄ := by
  apply WP.spec_bind (append_isomorphism_choice_spec before choice hRoom hValid hHead hTail)
  rintro ⟨index,after⟩ hConstructed
  simp only [uncurry_apply_pair]
  have hModel : optionalTree (alloc.vec.Vec.deref after) (some index) = matchedTree (alloc.vec.Vec.deref before) choice := by
    exact hConstructed.tree
  apply WP.spec_mono (reconstruct_isomorphism_choices_spec (alloc.vec.Vec.deref after) (some index)
    hConstructed.valid (by
      intro next he
      have hn : next = index := (Option.some.inj he).symm
      subst next
      exact hConstructed.root) (by simpa only [hModel] using hSize))
  intro output hOutput
  simpa only [hModel] using hOutput

/-- Independent affinity sum of an arena forest. The operation order matches
the intended head + tail + root contract; this is not an IEEE-754 model. -/
def affinityScore {K : Type*} [AddMonoid K] (affinity : U32 → U32 → K) : ChoiceTree → K
  | .nil => 0
  | .node ends head tail => affinityScore affinity head + affinityScore affinity tail + affinity ends.1.1 ends.1.2

theorem constructed_affinity_score {K : Type*} [AddMonoid K] (affinity : U32 → U32 → K)
    {before : alloc.vec.Vec IsomorphismChoice} {choice : IsomorphismChoice}
    {result : Usize × alloc.vec.Vec IsomorphismChoice} (h : Constructed before choice result) :
    affinityScore affinity (treeAt (alloc.vec.Vec.deref result.2) result.1.val) =
      affinityScore affinity (optionalTree (alloc.vec.Vec.deref before) choice.head) +
        affinityScore affinity (optionalTree (alloc.vec.Vec.deref before) choice.tail) +
          affinity choice.left_open choice.right_open := by
  rw [h.tree]
  rfl

theorem old_affinity_score_stable {K : Type*} [AddMonoid K] (affinity : U32 → U32 → K)
    {before : alloc.vec.Vec IsomorphismChoice} {choice : IsomorphismChoice}
    {result : Usize × alloc.vec.Vec IsomorphismChoice} (h : Constructed before choice result)
    (index : Nat) (hi : index < before.length) :
    affinityScore affinity (treeAt (alloc.vec.Vec.deref result.2) index) =
      affinityScore affinity (treeAt (alloc.vec.Vec.deref before) index) := by
  rw [h.stable index hi]

end SubtreeProofs.Rust.IsomorphismChoices

end
