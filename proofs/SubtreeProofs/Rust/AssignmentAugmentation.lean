module

public import SubtreeProofs.Rust.AssignmentAdjustmentInvariant
import Mathlib.Tactic

/-!
# Actual matching augmentation along an independent predecessor path

The path specification is a finite simple list of positive column indices,
whose last predecessor is the reserved column zero. It does not describe any
output of the program. The numerical frame records exact simultaneous shifts
of the original row pointers, including every untouched vector slot.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAugmentation

open AssignmentColumnScan AssignmentScanInvariant AssignmentAdjustmentInvariant

abbrev WalkState := alloc.vec.Vec Usize × Usize × Usize
abbrev WalkOutput := core.result.Result Unit AssignmentError × alloc.vec.Vec Usize

/-- Consecutive path entries follow the input predecessor vector; the final
entry points to the reserved root zero. -/
def Follows (predecessor : Slice Usize) : List Nat → Prop
  | [] => True
  | col :: rest => predecessor.val[col]!.val = rest.headD 0 ∧ Follows predecessor rest

theorem follows_suffix (predecessor : Slice Usize) (before after : List Nat)
    (h : Follows predecessor (before++after)) : Follows predecessor after := by
  induction before with
  | nil => exact h
  | cons col rest ih => exact ih h.2

/-- A path is independent input data and has at most n distinct real columns. -/
def ValidPath (predecessor : Slice Usize) (n : Usize) (path : List Nat) : Prop :=
  path.Nodup ∧ (∀ col ∈ path, 0 < col ∧ col ≤ n.val) ∧ Follows predecessor path

theorem validPath_length_le (predecessor : Slice Usize) (n : Usize) (path : List Nat)
    (hvalid : ValidPath predecessor n path) : path.length ≤ n.val := by
  have hsub : path.toFinset ⊆ Finset.Icc 1 n.val := by
    intro col hcol
    have hb := hvalid.2.1 col (List.mem_toFinset.mp hcol)
    exact Finset.mem_Icc.mpr ⟨hb.1,hb.2⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hvalid.1, Nat.card_Icc] at hcard
  omega

/-- Mathematical pointer shift, reading every replacement from the original
vector. Indices outside the path retain their exact original value. -/
def shifted (initial : alloc.vec.Vec Usize) (predecessor : Slice Usize) (path : List Nat) (index : Nat) : Usize :=
  if index ∈ path then initial.val[predecessor.val[index]!.val]! else initial.val[index]!

theorem shifted_append (initial : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (before : List Nat) (col index : Nat) :
    shifted initial predecessor (before++[col]) index =
      if index = col then initial.val[predecessor.val[index]!.val]! else shifted initial predecessor before index := by
  by_cases he : index = col <;>
    simp only [shifted, List.mem_append, List.mem_singleton, he, or_true, or_false, ↓reduceIte]

theorem body_step_spec (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (column n pathLength : Usize) (hpositive : 0 < column.val) (hpathLength : pathLength.val < n.val)
    (hcol : column.val < matched.length) (hpred : column.val < predecessor.length)
    (hprevious : predecessor.val[column.val]!.val < matched.length) :
    augment_matching_loop.body predecessor n matched column pathLength ⦃ output =>
      ∃ previous nextLength : Usize, previous = predecessor.val[column.val]! ∧
        nextLength.val = pathLength.val+1 ∧
        output = .cont (matched.set column matched.val[previous.val]!, previous, nextLength) ⦄ := by
  unfold augment_matching_loop.body
  have hnonzero : column != 0#usize := by scalar_tac
  have hguard : ¬ pathLength >= n := by scalar_tac
  simp only [hnonzero, hguard, ↓reduceIte]
  apply WP.spec_bind (Usize.add_spec (x := pathLength) (y := 1#usize) (by scalar_tac))
  intro nextLength hnext
  apply WP.spec_bind (Slice.index_usize_spec predecessor column hpred)
  intro previous hPrevious
  have he : previous = predecessor.val[column.val]! := by
    simpa only [getElem!_pos predecessor.val column.val hpred] using hPrevious
  have hprev : previous.val < matched.length := by simpa only [he] using hprevious
  simp only [alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec matched previous hprev)
  intro value hValue
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec matched column hcol)
  rintro ⟨_,back⟩ ⟨_,hback⟩
  simp only [uncurry_apply_pair, WP.spec_ok]
  refine ⟨previous,nextLength,he,by simpa using hnext,?_⟩
  simpa only [hback,getElem!_pos matched.val previous.val hprev] using
    congrArg (fun value => ControlFlow.cont (matched.set column value,previous,nextLength)) hValue

theorem body_done_spec (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (column n pathLength : Usize) (hzero : column.val = 0) :
    augment_matching_loop.body predecessor n matched column pathLength ⦃ output =>
      output = .done (core.result.Result.Ok (),matched) ⦄ := by
  unfold augment_matching_loop.body
  have he : column = 0#usize := by scalar_tac
  simp [he]

def WalkInvariant (initial : alloc.vec.Vec Usize) (predecessor : Slice Usize) (path : List Nat)
    (state : WalkState) : Prop :=
  ∃ before after : List Nat, path = before++after ∧ state.2.1.val = after.headD 0 ∧
    state.2.2.val = before.length ∧ Frame initial state.1 id (shifted initial predecessor before)

/-- The actual path walk realizes an exact simultaneous shift of the original
pointers. A valid simple predecessor path provides a termination bound and
rules out the source's path-length error. -/
theorem augment_matching_spec (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (column n : Usize) (path : List Nat) (hvalid : ValidPath predecessor n path)
    (hcol : column.val = path.headD 0)
    (hmatched : n.val < matched.length) (hpred : n.val < predecessor.length) :
    augment_matching matched predecessor column n ⦃ output =>
      output.1 = core.result.Result.Ok () ∧ Frame matched output.2 id (shifted matched predecessor path) ⦄ := by
  have hlength := validPath_length_le predecessor n path hvalid
  unfold augment_matching augment_matching_loop
  apply loop.spec_decr_nat (fun state => n.val-state.2.2.val)
    (WalkInvariant matched predecessor path)
    (fun (output : WalkOutput) => output.1 = core.result.Result.Ok () ∧ Frame matched output.2 id (shifted matched predecessor path)) _ _ ?_ ?_
  · rintro ⟨current,cursor,pathLength⟩ ⟨before,after,hpath,hcursor,hlen,hframe⟩
    dsimp only at hcursor hlen hframe ⊢
    have hnodup : (before++after).Nodup := hpath ▸ hvalid.1
    have hfollow := follows_suffix predecessor before after (hpath ▸ hvalid.2.2)
    cases after with
    | nil =>
      have he : cursor.val = 0 := hcursor
      apply WP.spec_mono (body_done_spec current predecessor cursor n pathLength he)
      intro output houtput
      subst output
      have hb : before = path := by simpa only [List.append_nil] using hpath.symm
      exact ⟨rfl, by simpa only [hb] using hframe⟩
    | cons col rest =>
      have hmember : col ∈ path := by rw [hpath]; simp
      have hc := hvalid.2.1 col hmember
      have hcv : cursor.val = col := hcursor
      have hprevious := hfollow.1
      have hprevBound : predecessor.val[col]!.val ≤ n.val := by
        cases rest with
        | nil =>
          have hz : predecessor.val[col]!.val = 0 := hprevious
          omega
        | cons next tail =>
          have hnext : next ∈ path := by rw [hpath]; simp
          simpa only [List.headD_cons] using hprevious.trans_le (hvalid.2.1 next hnext).2
      have hnotPrevious : predecessor.val[col]!.val ∉ before := by
        rw [hprevious]
        cases rest with
        | nil =>
          intro hzero
          have hm : 0 ∈ path := by rw [hpath]; exact List.mem_append_left _ hzero
          exact (Nat.lt_irrefl 0) (hvalid.2.1 0 hm).1
        | cons next tail =>
          simp only [List.headD_cons]
          have hdisjoint := (List.nodup_append.mp hnodup).2.2
          intro hm
          exact hdisjoint next hm next (by simp) rfl
      have hold : current.val[predecessor.val[col]!.val]! = matched.val[predecessor.val[col]!.val]! := by
        simpa only [id_eq, shifted, hnotPrevious, ↓reduceIte] using
          hframe.2 (predecessor.val[col]!.val) (lt_of_le_of_lt hprevBound hmatched)
      have hlenBound : pathLength.val < n.val := by
        have htotal : before.length + (col::rest).length ≤ n.val := by simpa only [hpath, List.length_append] using hlength
        simp only [List.length_cons] at htotal
        omega
      apply WP.spec_mono (body_step_spec current predecessor cursor n pathLength (by omega) hlenBound
        (by rw [hframe.1]; omega) (by omega)
        (by rw [hframe.1,hcv]; exact lt_of_le_of_lt hprevBound hmatched))
      rintro output ⟨previous,nextLength,he,hnext,houtput⟩
      subst output
      have hePrevious : previous.val = rest.headD 0 := by rw [he,hcv]; exact hprevious
      have hnewFrame : Frame matched (current.set cursor current.val[previous.val]!) id
          (shifted matched predecessor (before++[col])) := by
        apply frame_set matched current id _ _ cursor current.val[previous.val]! hframe (by omega)
        · rw [shifted_append, hcv]
          simp only [ite_true, id_eq,he,hcv]
          exact hold
        · intro other _ hne
          rw [shifted_append]
          apply ite_eq_right
          simpa only [hcv] using hne
      dsimp only [WalkInvariant]
      refine ⟨⟨before++[col],rest,?_,hePrevious,?_,hnewFrame⟩,by omega⟩
      · simpa only [List.append_assoc, List.singleton_append] using hpath
      · simp only [List.length_append,List.length_singleton]
        omega
  · exact ⟨[],path,by simp,hcol,by simp,by simp [Frame,shifted]⟩

end SubtreeProofs.Rust.AssignmentAugmentation

end
