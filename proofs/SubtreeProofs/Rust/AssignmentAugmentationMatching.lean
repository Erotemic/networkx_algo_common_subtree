module

public import SubtreeProofs.Rust.AssignmentAugmentationPath
public import SubtreeProofs.Rust.AssignmentPredecessorPaths
public import SubtreeProofs.Shared.AssignmentAugmentation
import Mathlib.Tactic

/-!
# Actual augmentation preserves and extends the independent partial assignment

The source's row-pointer vector is interpreted as a partial injective assignment.
A simple predecessor path starts at an unmatched real column and ends at the
reserved fresh row. The returned vector covers exactly one additional row.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAugmentationMatching

open AssignmentAugmentation AssignmentAugmentationPath AssignmentPredecessorPaths AssignmentAdjustmentInvariant

def pointers (matched : alloc.vec.Vec Usize) (col : Nat) : Nat := matched.val[col]!.val

theorem shifted_value (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize) (path : List Nat) (col : Nat) :
    (shifted matched predecessor path col).val = pointers matched (route predecessor path col) := by
  by_cases hm : col ∈ path <;> simp only [shifted,route,hm,↓reduceIte,pointers]

/-- The vector frame established by the actual walk extends the independent
partial assignment by the fresh row in reserved slot zero. -/
theorem frame_preserves_partial (matched current : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (n : Usize) (filled head : Nat) (rest : List Nat)
    (hvalid : ValidPath predecessor n (head::rest)) (hmatched : n.val < matched.length)
    (hframe : Frame matched current id (shifted matched predecessor (head::rest)))
    (hpartial : Assignment.PartialRows n.val filled (pointers matched))
    (hroot : pointers matched 0 = filled+1) (hterminal : pointers matched head = 0) :
    Assignment.PartialRows n.val (filled+1) (pointers current) := by
  have hroute := Assignment.reassign_preserves_partial n.val filled head (pointers matched)
    (route predecessor (head::rest)) hpartial hroot hterminal
    (route_bound predecessor n head rest hvalid)
    (route_injective predecessor n head rest hvalid)
    (route_surjective predecessor n head rest hvalid)
  apply hroute.congr
  intro col hp hb
  have h := congrArg UScalar.val (hframe.2 col (lt_of_le_of_lt hb hmatched))
  simp only [id_eq, shifted_value] at h
  exact h.symm

/-- Actual successful augmentation adds the fresh row to the represented
partial matching. Existing rows remain represented exactly once. -/
theorem augment_matching_partial_spec (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (column n : Usize) (filled : Nat) (path : List Nat)
    (hvalid : ValidPath predecessor n path) (hcol : column.val = path.headD 0) (hpositive : 0 < column.val)
    (hmatched : n.val < matched.length) (hpred : n.val < predecessor.length)
    (hpartial : Assignment.PartialRows n.val filled (pointers matched))
    (hroot : pointers matched 0 = filled+1) (hterminal : pointers matched column.val = 0) :
    augment_matching matched predecessor column n ⦃ output =>
      output.1 = core.result.Result.Ok () ∧
        Frame matched output.2 id (shifted matched predecessor path) ∧
          Assignment.PartialRows n.val (filled+1) (pointers output.2) ⦄ := by
  apply WP.spec_mono (augment_matching_spec matched predecessor column n path hvalid hcol hmatched hpred)
  rintro output ⟨hsuccess,hframe⟩
  refine ⟨hsuccess,hframe,?_⟩
  cases path with
  | nil => simp only [List.headD_nil] at hcol; omega
  | cons head rest =>
    have he : column.val = head := hcol
    exact frame_preserves_partial matched output.2 predecessor n filled head rest hvalid hmatched hframe hpartial hroot
      (by simpa only [he] using hterminal)

/-- Local ranked-forest properties suffice for actual matching extension;
no predecessor path needs to be passed to the program or supplied separately. -/
theorem augment_matching_ranked_partial_spec (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (column n : Usize) (filled : Nat) (vertices : Finset Nat) (rank : Nat → Nat)
    (hranked : Ranked predecessor n vertices rank) (hcol : column.val ∈ vertices) (hpositive : 0 < column.val)
    (hmatched : n.val < matched.length) (hpred : n.val < predecessor.length)
    (hpartial : Assignment.PartialRows n.val filled (pointers matched))
    (hroot : pointers matched 0 = filled+1) (hterminal : pointers matched column.val = 0) :
    augment_matching matched predecessor column n ⦃ output =>
      output.1 = core.result.Result.Ok () ∧
        Assignment.PartialRows n.val (filled+1) (pointers output.2) ⦄ := by
  obtain ⟨path,hvalid,hhead,_⟩ := exists_validPath predecessor n vertices rank hranked column.val hcol
  apply WP.spec_mono (augment_matching_partial_spec matched predecessor column n filled path hvalid hhead.symm hpositive
    hmatched hpred hpartial hroot hterminal)
  rintro output ⟨hsuccess,_,hpartial⟩
  exact ⟨hsuccess,hpartial⟩


/-- Tight predecessor edges replace the path's old edges; every edge outside
the path retains its old tightness in the actual returned vector. -/
theorem frame_preserves_tight {K : Type*} [Add K] (matched current : alloc.vec.Vec Usize)
    (predecessor : Slice Usize) (n : Usize) (path : List Nat)
    (matrix : Nat → Nat → K) (rows columns : Nat → K) (hmatched : n.val < matched.length)
    (hframe : Frame matched current id (shifted matched predecessor path))
    (htight : Assignment.TightPointers n.val matrix rows columns (pointers matched))
    (hpath : ∀ col ∈ path, rows (pointers matched predecessor.val[col]!.val) + columns col =
      matrix (pointers matched predecessor.val[col]!.val) col) :
    Assignment.TightPointers n.val matrix rows columns (pointers current) := by
  intro col hp hb hn
  have hvalue := congrArg UScalar.val (hframe.2 col (lt_of_le_of_lt hb hmatched))
  simp only [id_eq,shifted_value] at hvalue
  change pointers current col = pointers matched (route predecessor path col) at hvalue
  rw [hvalue] at hn ⊢
  by_cases hm : col ∈ path
  · simpa only [route,hm,↓reduceIte] using hpath col hm
  · simp only [route,hm,↓reduceIte] at hn ⊢
    exact htight col hp hb hn

/-- A ranked predecessor forest with tight edges suffices for actual
augmentation to extend the partial assignment and retain all matched-edge
tightness simultaneously. -/
theorem augment_matching_ranked_tight_spec {K : Type*} [Add K]
    (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (column n : Usize) (filled : Nat) (vertices : Finset Nat) (rank : Nat → Nat)
    (hranked : Ranked predecessor n vertices rank) (hcol : column.val ∈ vertices) (hpositive : 0 < column.val)
    (hmatched : n.val < matched.length) (hpred : n.val < predecessor.length)
    (hpartial : Assignment.PartialRows n.val filled (pointers matched))
    (hroot : pointers matched 0 = filled+1) (hterminal : pointers matched column.val = 0)
    (matrix : Nat → Nat → K) (rows columns : Nat → K)
    (htight : Assignment.TightPointers n.val matrix rows columns (pointers matched))
    (hforest : ∀ col ∈ vertices, col ≠ 0 →
      rows (pointers matched predecessor.val[col]!.val) + columns col =
        matrix (pointers matched predecessor.val[col]!.val) col) :
    augment_matching matched predecessor column n ⦃ output =>
      output.1 = core.result.Result.Ok () ∧
        Assignment.PartialRows n.val (filled+1) (pointers output.2) ∧
          Assignment.TightPointers n.val matrix rows columns (pointers output.2) ∧ output.2.length = matched.length ⦄ := by
  obtain ⟨path,hvalid,hhead,hentries⟩ := exists_validPath predecessor n vertices rank hranked column.val hcol
  apply WP.spec_mono (augment_matching_partial_spec matched predecessor column n filled path hvalid hhead.symm hpositive
    hmatched hpred hpartial hroot hterminal)
  rintro output ⟨hsuccess,hframe,hpartial⟩
  refine ⟨hsuccess,hpartial,frame_preserves_tight matched output.2 predecessor n path matrix rows columns hmatched hframe htight ?_,hframe.1⟩
  intro col hc
  have hp := (hvalid.2.1 col hc).1
  exact hforest col (hentries col hc).1 (by omega)

end SubtreeProofs.Rust.AssignmentAugmentationMatching

end
