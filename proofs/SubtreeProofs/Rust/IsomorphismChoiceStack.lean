module

public import SubtreeProofs.Rust.IsomorphismChoiceModel
import Mathlib.Tactic

/-! # Actual reusable stack slots in production isomorphism reconstruction -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_ordered_core.isomorphism_choices

namespace SubtreeProofs.Rust.IsomorphismChoices

def active (pending : alloc.vec.Vec Visit) (length : Usize) : List Visit :=
  pending.val.take length.val

theorem older_child_spec (child : Option Usize) (parent : Usize)
    (h : ∀ index, child = some index → index.val < parent.val) :
    older_child child parent ⦃ result => result = true ⦄ := by
  cases child with
  | none => simp [older_child]
  | some index =>
    have hv := h index rfl
    have hi : index < parent := by scalar_tac
    simp [older_child,hi]

/-- Actual overwrite/append preserves exactly the logical active prefix, and
safely advances the cursor. Spare slots can contain arbitrary old tasks. -/
theorem push_visit_spec (pending : alloc.vec.Vec Visit) (length : Usize) (visit : Visit)
    (hl : length.val ≤ pending.length) (hb : length.val < Usize.max) :
    push_visit pending length visit ⦃ result =>
      result.2.val = length.val+1 ∧ result.2.val ≤ result.1.length ∧
        active result.1 result.2 = active pending length ++ [visit] ⦄ := by
  unfold push_visit
  have hn := alloc.vec.Vec.len_val pending
  have hWrite :
      (if length < alloc.vec.Vec.len pending then do
        let (_,back) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Visit) pending length
        ok (back visit)
      else alloc.vec.Vec.push pending visit) ⦃ output =>
        length.val+1 ≤ output.length ∧
        output.val.take (length.val+1) = active pending length ++ [visit] ⦄ := by
    split
    · rename_i hi
      have hlt : length.val < pending.length := by scalar_tac
      simp only [alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec pending length hlt)
      rintro ⟨_,back⟩ ⟨_,hBack⟩
      simp only [uncurry_apply_pair,hBack,WP.spec_ok,alloc.vec.Vec.set_length]
      refine ⟨by omega,?_⟩
      rw [alloc.vec.Vec.set_val_eq]
      rw [List.take_succ_eq_append_getElem (by simpa only [List.length_set,alloc.vec.Vec.length] using hlt),
        List.take_set_of_le (le_refl length.val),List.getElem_set_self]
      rfl
    · rename_i hi
      have he : length.val = pending.length := by scalar_tac
      apply WP.spec_mono (alloc.vec.Vec.push_spec pending visit (by change pending.length < Usize.max; omega))
      intro output hOutput
      simp only [alloc.vec.Vec.length,hOutput,List.length_append,List.length_singleton]
      constructor
      · change length.val ≤ pending.val.length at hl
        omega
      · simp [active,he,alloc.vec.Vec.length]
  apply WP.spec_bind hWrite
  intro output hOutput
  apply WP.spec_bind (Usize.add_spec (x := length) (y := 1#usize) (by scalar_tac))
  intro next hNext
  have hnext : next.val = length.val+1 := by simpa using hNext
  simp only [WP.spec_ok]
  exact ⟨hnext,by rw [hnext]; exact hOutput.1,by simpa only [active,hnext] using hOutput.2⟩

def optionalVisits (child : Option Usize) : List Visit := child.toList.map Visit.Pair

theorem optional_push_spec (pending : alloc.vec.Vec Visit) (length : Usize) (child : Option Usize)
    (hl : length.val ≤ pending.length) (hb : length.val+(optionalVisits child).length ≤ Usize.max) :
    (match child with
      | none => ok (pending,length)
      | some index => push_visit pending length (Visit.Pair index)) ⦃ result =>
      result.2.val = length.val+(optionalVisits child).length ∧ result.2.val ≤ result.1.length ∧
        active result.1 result.2 = active pending length ++ optionalVisits child ⦄ := by
  cases child with
  | none => simp only [optionalVisits,Option.toList_none,List.map_nil,List.length_nil,Nat.add_zero,
      List.append_nil,WP.spec_ok,eq_self,true_and,and_true]; exact hl
  | some index =>
    simp only [optionalVisits,Option.toList_some,List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hb ⊢
    exact push_visit_spec pending length (Visit.Pair index) hl (by omega)

theorem optionalVisits_valid (choices : Slice IsomorphismChoice) (child : Option Usize)
    (h : ∀ index, child = some index → index.val < choices.length) :
    ValidStack choices (optionalVisits child) := by
  cases child with
  | none => simp [ValidStack,optionalVisits]
  | some index => simpa [ValidStack,optionalVisits,ValidVisit] using h index rfl

theorem stackTokens_optional (choices : Slice IsomorphismChoice) (child : Option Usize) :
    stackTokens choices (optionalVisits child) = tokens (optionalTree choices child) := by
  cases child <;> simp [stackTokens,optionalVisits,optionalTree,visitTokens,tokens]

def childTasks (choice : IsomorphismChoice) : List Visit :=
  optionalVisits choice.tail ++ [Visit.Close choice.left_close choice.right_close] ++ optionalVisits choice.head

theorem stackTokens_append_list (choices : Slice IsomorphismChoice) (left right : List Visit) :
    stackTokens choices (left ++ right) = stackTokens choices right ++ stackTokens choices left := by
  simp [stackTokens,List.reverse_append]

theorem pair_tokens (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (index : Usize) (hi : index.val < choices.length) :
    visitTokens choices (Visit.Pair index) =
      (choices.val[index.val].left_open,choices.val[index.val].right_open) ::
        stackTokens choices (childTasks choices.val[index.val]) := by
  rw [visitTokens,treeAt_eq choices index.val hValid hi]
  simp only [tokens,childTasks,stackTokens_append_list,stackTokens_optional]
  simp [stackTokens,visitTokens]

theorem childTasks_valid (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (index : Usize) (hi : index.val < choices.length) :
    ValidStack choices (childTasks choices.val[index.val]) := by
  have hh := optionalVisits_valid choices choices.val[index.val].head
    (fun child hc => ((hValid index.val hi).1 child hc).trans hi)
  have ht := optionalVisits_valid choices choices.val[index.val].tail
    (fun child hc => ((hValid index.val hi).2 child hc).trans hi)
  intro visit hm
  simp only [childTasks,List.mem_append,List.mem_singleton] at hm
  rcases hm with (hm | rfl) | hm
  · exact ht visit hm
  · trivial
  · exact hh visit hm

/-- The exact enqueue fragment of the actual pair branch, including each
checked cursor increment and preservation of arbitrary inactive slots. -/
theorem push_children_spec (pending : alloc.vec.Vec Visit) (length : Usize)
    (left right : alloc.vec.Vec U32) (choice : IsomorphismChoice)
    (hl : length.val ≤ pending.length) (hb : length.val+(childTasks choice).length ≤ Usize.max) :
    (do
      let (pending1,length1) ← match choice.tail with
        | none => ok (pending,length)
        | some tail => push_visit pending length (Visit.Pair tail)
      let (pending2,length2) ← push_visit pending1 length1 (Visit.Close choice.left_close choice.right_close)
      match choice.head with
      | none => ok (cont (pending2,left,right,length2) :
          ControlFlow (alloc.vec.Vec Visit × alloc.vec.Vec U32 × alloc.vec.Vec U32 × Usize)
            (Option (alloc.vec.Vec U32 × alloc.vec.Vec U32)))
      | some head => do
        let (pending3,length3) ← push_visit pending2 length2 (Visit.Pair head)
        ok (cont (pending3,left,right,length3))) ⦃ output => ∃ result count,
      output = cont (result,left,right,count) ∧ count.val = length.val+(childTasks choice).length ∧
      count.val ≤ result.length ∧ active result count = active pending length ++ childTasks choice ⦄ := by
  have hsize : (childTasks choice).length =
      (optionalVisits choice.tail).length+1+(optionalVisits choice.head).length := by
    simp only [childTasks,List.length_append,List.length_singleton]
  apply WP.spec_bind (optional_push_spec pending length choice.tail hl (by omega))
  rintro ⟨pending1,length1⟩ ⟨hCount1,hBound1,hActive1⟩
  dsimp only at hCount1 hBound1 hActive1
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (push_visit_spec pending1 length1 (Visit.Close choice.left_close choice.right_close) hBound1 (by omega))
  rintro ⟨pending2,length2⟩ ⟨hCount2,hBound2,hActive2⟩
  dsimp only at hCount2 hBound2 hActive2
  simp only [uncurry_apply_pair]
  cases he : choice.head with
  | none =>
    simp only [WP.spec_ok]
    refine ⟨pending2,length2,rfl,?_,hBound2,?_⟩
    · have hhead : (optionalVisits choice.head).length = 0 := by simp [he,optionalVisits]
      rw [hhead] at hsize
      omega
    · rw [hActive2,hActive1]
      simp [childTasks,he,optionalVisits,List.append_assoc]
  | some head =>
    have hhead : (optionalVisits choice.head).length = 1 := by simp [he,optionalVisits]
    apply WP.spec_bind (push_visit_spec pending2 length2 (Visit.Pair head) hBound2 (by omega))
    rintro ⟨pending3,length3⟩ ⟨hCount3,hBound3,hActive3⟩
    dsimp only at hCount3 hBound3 hActive3
    simp only [uncurry_apply_pair,WP.spec_ok]
    refine ⟨pending3,length3,rfl,by omega,hBound3,?_⟩
    rw [hActive3,hActive2,hActive1]
    simp [childTasks,he,optionalVisits,List.append_assoc]

end SubtreeProofs.Rust.IsomorphismChoices

end
