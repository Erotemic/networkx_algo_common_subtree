module

public import SubtreeProofs.Rust.SparsePathCopy
import Mathlib.Tactic

/-! # Exact checked array writes of one actual sparse path-flip iteration -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

abbrev FlipState := alloc.vec.Vec Usize × Usize × Usize × Bool × Option AssignmentError

def afterFlip (completed predecessor : Slice Usize) (root column : Usize)
    (assignment : alloc.vec.Vec Usize) (next : Usize) : FlipState :=
  let row := predecessor.val[column.val]!
  (assignment.set row column,if row = root then column else completed.val[row.val]!,next,decide (row = root),none)

/-- One source flip writes the original discovered column into its predecessor
row and either stops at the root or follows the old assignment to an earlier
positive rank. These local bounds are discharged from the actual certificate
and trace in the complete loop proof. -/
theorem flip_body_step_spec (completed predecessor discovery : Slice Usize) (root n column cursor : Usize)
    (assignment : alloc.vec.Vec Usize) (hc : cursor.val < n.val) (hcol : column.val < n.val)
    (hl : completed.length = n.val) (hp : predecessor.length = n.val) (hd : discovery.length = n.val)
    (ha : assignment.length = n.val)
    (hr : predecessor.val[column.val]!.val < n.val) (hRank : 0 < discovery.val[column.val]!.val)
    (hParent : predecessor.val[column.val]! ≠ root →
      completed.val[predecessor.val[column.val]!.val]!.val < n.val ∧
      0 < discovery.val[completed.val[predecessor.val[column.val]!.val]!.val]!.val ∧
      discovery.val[completed.val[predecessor.val[column.val]!.val]!.val]!.val < discovery.val[column.val]!.val) :
    sparse_search.flip_sparse_path_loop.body completed predecessor discovery root n assignment column cursor false none ⦃ result => ∃ next,
      next.val = cursor.val+1 ∧ result = .cont (afterFlip completed predecessor root column assignment next) ⦄ := by
  have hGuard : ¬ cursor ≥ n := by scalar_tac
  unfold sparse_search.flip_sparse_path_loop.body
  simp only [Bool.false_eq_true,↓reduceIte,core.option.Option.is_none,hGuard,bind_ok]
  apply WP.spec_bind (Usize.add_spec (x := cursor) (y := 1#usize) (by scalar_tac))
  intro next hNext
  apply WP.spec_bind (Slice.index_usize_spec predecessor column (by omega))
  intro row hRow
  have hrow : row = predecessor.val[column.val]! := by
    simpa only [getElem!_pos predecessor.val column.val (by change column.val < predecessor.length; omega)] using hRow
  have hrange : ¬ row ≥ n := by rw [hrow]; scalar_tac
  simp only [hrange,↓reduceIte]
  apply WP.spec_bind (Slice.index_usize_spec discovery column (by omega))
  intro rank hReadRank
  have hrank : rank = discovery.val[column.val]! := by
    simpa only [getElem!_pos discovery.val column.val (by change column.val < discovery.length; omega)] using hReadRank
  have hpos : rank ≠ 0#usize := by rw [hrank]; scalar_tac
  simp only [hpos,↓reduceIte,alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec assignment row (by rw [ha,hrow]; exact hr))
  rintro ⟨_,back⟩ ⟨_,hBack⟩
  simp only [uncurry_apply_pair]
  by_cases he : row = root
  · simp only [he,↓reduceIte]
    apply (WP.spec_ok _).mpr
    refine ⟨next,by simpa only [UScalar.ofNatCore_val_eq] using hNext,?_⟩
    simp only [afterFlip,← hrow,he,↓reduceIte,decide_true,hBack]
  · simp only [he,↓reduceIte]
    have hpar := hParent (by simpa only [← hrow] using he)
    apply WP.spec_bind (Slice.index_usize_spec completed row (by rw [hl,hrow]; exact hr))
    intro parent hReadParent
    have hparent : parent = completed.val[row.val]! := by
      simpa only [getElem!_pos completed.val row.val (by change row.val < completed.length; rw [hl,hrow]; exact hr)] using hReadParent
    have hparentRange : ¬ parent ≥ n := by rw [hparent,hrow]; scalar_tac
    simp only [hparentRange,↓reduceIte]
    apply WP.spec_bind (Slice.index_usize_spec discovery parent (by rw [hd,hparent,hrow]; exact hpar.1))
    intro parentRank hReadParentRank
    have hparentRank : parentRank = discovery.val[parent.val]! := by
      simpa only [getElem!_pos discovery.val parent.val (by change parent.val < discovery.length; rw [hd,hparent,hrow]; exact hpar.1)] using hReadParentRank
    have hpv : 0 < parentRank.val := by rw [hparentRank,hparent,hrow]; exact hpar.2.1
    have hparentPositive : parentRank ≠ 0#usize := by scalar_tac
    have hlt : parentRank.val < rank.val := by rw [hparentRank,hparent,hrow,hrank]; exact hpar.2.2
    have hLess : ¬ parentRank ≥ rank := by scalar_tac
    simp only [hparentPositive,hLess,↓reduceIte]
    apply (WP.spec_ok _).mpr
    refine ⟨next,by simpa only [UScalar.ofNatCore_val_eq] using hNext,?_⟩
    simp only [afterFlip,← hrow,he,↓reduceIte,decide_false,hBack,hparent]

end SubtreeProofs.Rust.SparseSearch

end
