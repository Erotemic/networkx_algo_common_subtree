module

public import SubtreeProofs.Shared.AssignmentSearchCapacity
public import SubtreeProofs.Rust.AssignmentAdjustmentInvariant
import Mathlib.Tactic

/-!
# Actual used-column vectors satisfy the independent search capacity bounds

An unfinished partial assignment supplies an unused free column. With the
fresh row at zero, its nonzero pointers are injective on every used column;
a further unvisited matched column makes the visit counter strictly below n.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentSearchCapacity

open AssignmentScanInvariant AssignmentAdjustmentInvariant

def UsedMatched (matched : Slice Usize) (used : Slice Bool) (n : Usize) : Prop :=
  ∀ col, col ≤ n.val → used.val[col]! = true → matched.val[col]!.val ≠ 0

theorem used_injective (matched : Slice Usize) (used : Slice Bool) (n : Usize) (filled : Nat)
    (hpartial : Assignment.PartialRows n.val filled (fun col => matched.val[col]!.val))
    (hroot : matched.val[0]!.val = filled+1) (hused : UsedMatched matched used n) : UsedInjective matched used n := by
  intro first hf hfu second hs _ he
  exact hpartial.with_root_injective hroot first hf (hused first hf hfu) second hs he

/-- The actual source's scan has an available positive unused column. -/
theorem unused_free_column (matched : Slice Usize) (used : Slice Bool) (n : Usize) (filled : Nat)
    (hpartial : Assignment.PartialRows n.val filled (fun col => matched.val[col]!.val))
    (hfilled : filled < n.val) (hused : UsedMatched matched used n) :
    ∃ col, 0 < col ∧ col ≤ n.val ∧ used.val[col]! = false ∧ matched.val[col]!.val = 0 := by
  obtain ⟨col,hp,hb,hfree⟩ := hpartial.exists_unmatched hfilled
  refine ⟨col,hp,hb,?_,hfree⟩
  cases hf : used.val[col]!
  · rfl
  · exact False.elim (hused col hb hf hfree)

/-- A real counter equal to the used-vector cardinality cannot trigger the
source's visit-limit failure before visiting a new matched column. -/
theorem visit_guard (matched : Slice Usize) (used : Slice Bool) (n : Usize) (filled : Nat)
    (visited column : Usize)
    (hpartial : Assignment.PartialRows n.val filled (fun col => matched.val[col]!.val))
    (hroot : matched.val[0]!.val = filled+1) (hfilled : filled < n.val) (hused : UsedMatched matched used n)
    (hvisited : visited.val = (usedIndices used (n.val+1)).card)
    (hcolumn : column.val ≤ n.val) (hrow : matched.val[column.val]!.val ≠ 0) (hnew : used.val[column.val]! = false) :
    visited.val < n.val := by
  rw [hvisited]
  apply hpartial.used_card_lt hroot hfilled (usedIndices used (n.val+1))
  · intro col hc
    have hm := (mem_usedIndices used _ _).mp hc
    have hb : col ≤ n.val := by omega
    exact ⟨hb,hused col hb hm.2⟩
  · exact hcolumn
  · exact hrow
  · intro hm
    have hh := (mem_usedIndices used _ _).mp hm
    rw [hnew] at hh
    exact Bool.noConfusion hh.2

/-- The source's boolean write inserts precisely the visited column into the
mathematical candidate set, leaving every other membership unchanged. -/
theorem usedIndices_set_true (used : alloc.vec.Vec Bool) (n column : Usize)
    (hcolumn : column.val ≤ n.val) (hlen : n.val < used.length) :
    usedIndices (alloc.vec.Vec.deref (used.set column true)) (n.val+1) =
      insert column.val (usedIndices (alloc.vec.Vec.deref used) (n.val+1)) := by
  ext index
  simp only [mem_usedIndices,Finset.mem_insert,alloc.vec.Vec.deref,Slice.from_val]
  by_cases he : index = column.val
  · subst index
    rw [vec_set_self used column true (lt_of_le_of_lt hcolumn hlen)]
    simp only [eq_self,true_or,iff_true,and_true]
    omega
  · by_cases hb : index < n.val+1
    · have hi : index < used.length := by omega
      rw [vec_set_other used column true index hi (Ne.symm he)]
      simp only [he,false_or]
    · simp only [he,false_or,hb,false_and]

end SubtreeProofs.Rust.AssignmentSearchCapacity

end
