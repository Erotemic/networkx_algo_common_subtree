module

public import SubtreeProofs.Rust.IsomorphismChoiceStack
import Mathlib.Tactic

/-! # Source loop for the production ordered-isomorphism witness emitter -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_ordered_core.isomorphism_choices

namespace SubtreeProofs.Rust.IsomorphismChoices

abbrev EmissionState := alloc.vec.Vec Visit × alloc.vec.Vec U32 × alloc.vec.Vec U32 × Usize

def remaining (choices : Slice IsomorphismChoice) (state : EmissionState) : List (U32 × U32) :=
  stackTokens choices (active state.1 state.2.2.2)

structure EmissionInvariant (choices : Slice IsomorphismChoice) (targetLeft targetRight : List U32)
    (state : EmissionState) : Prop where
  cursor : state.2.2.2.val ≤ state.1.length
  stack : ValidStack choices (active state.1 state.2.2.2)
  left : state.2.1.val ++ (remaining choices state).map Prod.fst = targetLeft
  right : state.2.2.1.val ++ (remaining choices state).map Prod.snd = targetRight

def EmissionPost (targetLeft targetRight : List U32)
    (output : Option (alloc.vec.Vec U32 × alloc.vec.Vec U32)) : Prop :=
  ∃ left right, output = some (left,right) ∧ left.val = targetLeft ∧ right.val = targetRight

def EmissionBodyPost (choices : Slice IsomorphismChoice) (targetLeft targetRight : List U32)
    (old : EmissionState) : ControlFlow EmissionState (Option (alloc.vec.Vec U32 × alloc.vec.Vec U32)) → Prop
  | .done output => EmissionPost targetLeft targetRight output
  | .cont next => EmissionInvariant choices targetLeft targetRight next ∧
      (remaining choices next).length < (remaining choices old).length

theorem emits_one (choices : Slice IsomorphismChoice) (targetLeft targetRight : List U32)
    (old next : EmissionState) (leftToken rightToken : U32)
    (h : EmissionInvariant choices targetLeft targetRight old)
    (hCursor : next.2.2.2.val ≤ next.1.length)
    (hStack : ValidStack choices (active next.1 next.2.2.2))
    (hTokens : remaining choices old = (leftToken,rightToken) :: remaining choices next)
    (hLeft : next.2.1.val = old.2.1.val ++ [leftToken])
    (hRight : next.2.2.1.val = old.2.2.1.val ++ [rightToken]) :
    EmissionInvariant choices targetLeft targetRight next ∧
      (remaining choices next).length < (remaining choices old).length := by
  constructor
  · refine ⟨hCursor,hStack,?_,?_⟩
    · rw [← h.left,hTokens,hLeft]
      simp [List.append_assoc]
    · rw [← h.right,hTokens,hRight]
      simp [List.append_assoc]
  · rw [hTokens,List.length_cons]
    omega

/-- Every actual iteration emits one token in each input, preserves the
remaining forest interpretation and decreases its length. All actual source
reads, slot writes, pushes and checked cursor arithmetic are discharged. -/
theorem emission_body_spec (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (targetLeft targetRight : List U32) (hLeftBound : targetLeft.length ≤ Usize.max)
    (hRightBound : targetRight.length ≤ Usize.max)
    (pending : alloc.vec.Vec Visit) (left right : alloc.vec.Vec U32) (length : Usize)
    (h : EmissionInvariant choices targetLeft targetRight (pending,left,right,length)) :
    reconstruct_isomorphism_choices_loop.body choices pending left right length ⦃ output =>
      EmissionBodyPost choices targetLeft targetRight (pending,left,right,length) output ⦄ := by
  have hCursor : length.val ≤ pending.length := h.cursor
  have hLeftSize := congrArg List.length h.left
  have hRightSize := congrArg List.length h.right
  simp only [List.length_append,List.length_map] at hLeftSize hRightSize
  have hBudget : (remaining choices (pending,left,right,length)).length ≤ Usize.max := by omega
  unfold reconstruct_isomorphism_choices_loop.body
  split
  · rename_i hPositive
    have hpositive : 0 < length.val := by scalar_tac
    apply WP.spec_bind (Usize.sub_spec (x := length) (y := 1#usize) (by scalar_tac))
    intro top hTop
    have htop : top.val+1 = length.val := by scalar_tac
    have hi : top.val < pending.length := by omega
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec pending top hi)
    intro visit hVisit
    have hActive : active pending length = active pending top ++ [visit] := by
      unfold active
      rw [← htop,List.take_succ_eq_append_getElem (by simpa only [alloc.vec.Vec.length] using hi),← hVisit]
    have hRest : ValidStack choices (active pending top) := by
      intro task hm
      apply h.stack task
      rw [hActive]
      exact List.mem_append_left _ hm
    have hv : ValidVisit choices visit := by
      apply h.stack visit
      rw [hActive]
      simp
    have hOld : remaining choices (pending,left,right,length) =
        visitTokens choices visit ++ stackTokens choices (active pending top) := by
      unfold remaining
      rw [hActive,stackTokens_append]
    have hNonempty := visit_tokens_nonempty choices hValid visit hv
    have hLeftRoom : left.val.length < Usize.max := by
      have hh := congrArg List.length hOld
      simp only [List.length_append] at hh
      change left.val.length+_ = _ at hLeftSize
      omega
    have hRightRoom : right.val.length < Usize.max := by
      have hh := congrArg List.length hOld
      simp only [List.length_append] at hh
      change right.val.length+_ = _ at hRightSize
      omega
    cases visit with
    | Close leftToken rightToken =>
      simp only
      apply WP.spec_bind (alloc.vec.Vec.push_spec left leftToken hLeftRoom)
      intro left1 hLeft1
      apply WP.spec_bind (alloc.vec.Vec.push_spec right rightToken hRightRoom)
      intro right1 hRight1
      simp only [WP.spec_ok,EmissionBodyPost]
      apply emits_one choices targetLeft targetRight (pending,left,right,length)
        (pending,left1,right1,top) leftToken rightToken h
        (by change top.val ≤ pending.length; omega) hRest _ hLeft1 hRight1
      simpa only [remaining,visitTokens,List.singleton_append] using hOld
    | Pair index =>
      simp only
      have hindex : index.val < choices.length := hv
      have hsmall : ¬ index ≥ Slice.len choices := by have hh := Slice.len_val choices; scalar_tac
      simp only [hsmall,↓reduceIte]
      apply WP.spec_bind (Slice.index_usize_spec choices index hindex)
      intro choice hChoice
      have hHead : ∀ child, choice.head = some child → child.val < index.val := by
        rw [hChoice]
        exact (hValid index.val hindex).1
      have hTail : ∀ child, choice.tail = some child → child.val < index.val := by
        rw [hChoice]
        exact (hValid index.val hindex).2
      apply WP.spec_bind (older_child_spec choice.head index hHead)
      intro headOK hHeadOK
      simp only [hHeadOK,↓reduceIte]
      apply WP.spec_bind (older_child_spec choice.tail index hTail)
      intro tailOK hTailOK
      simp only [hTailOK,↓reduceIte]
      have hTasks : ValidStack choices (childTasks choice) := by
        rw [hChoice]
        exact childTasks_valid choices hValid index hindex
      have hNewStack : ValidStack choices (active pending top ++ childTasks choice) := by
        intro task hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hRest task hm
        · exact hTasks task hm
      have hTokens : remaining choices (pending,left,right,length) =
          (choice.left_open,choice.right_open) ::
            stackTokens choices (active pending top ++ childTasks choice) := by
        rw [hOld,pair_tokens choices hValid index hindex,← hChoice,stackTokens_append_list]
        rfl
      have hStackBound := stack_length_bound choices hValid _ hNewStack
      have hRestLength : (active pending top).length = top.val := by
        simp only [active,List.length_take]
        exact Nat.min_eq_left (by change top.val ≤ pending.length; omega)
      have hTaskBudget : top.val+(childTasks choice).length ≤ Usize.max := by
        have hTokenSize := congrArg List.length hTokens
        simp only [List.length_cons] at hTokenSize
        rw [List.length_append,hRestLength] at hStackBound
        omega
      apply WP.spec_bind (alloc.vec.Vec.push_spec left choice.left_open hLeftRoom)
      intro left1 hLeft1
      apply WP.spec_bind (alloc.vec.Vec.push_spec right choice.right_open hRightRoom)
      intro right1 hRight1
      apply WP.spec_mono (push_children_spec pending top left1 right1 choice (by omega) hTaskBudget)
      rintro output ⟨result,count,rfl,hCount,hCountBound,hResult⟩
      simp only [EmissionBodyPost]
      apply emits_one choices targetLeft targetRight (pending,left,right,length)
        (result,left1,right1,count) choice.left_open choice.right_open h hCountBound _ _ hLeft1 hRight1
      · simpa only [hResult] using hNewStack
      · simpa only [remaining,hResult] using hTokens
  · rename_i hStopped
    have hz : length.val = 0 := by scalar_tac
    have hEmpty : remaining choices (pending,left,right,length) = [] := by
      simp [remaining,active,hz]
    simp only [WP.spec_ok,EmissionBodyPost,EmissionPost]
    refine ⟨left,right,rfl,?_,?_⟩
    · simpa only [hEmpty,List.map_nil,List.append_nil] using h.left
    · simpa only [hEmpty,List.map_nil,List.append_nil] using h.right

end SubtreeProofs.Rust.IsomorphismChoices

end
