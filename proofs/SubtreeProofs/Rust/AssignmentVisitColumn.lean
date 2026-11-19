module

public import SubtreeProofs.Rust.AssignmentDiscoveryRanks
public import SubtreeProofs.Rust.AssignmentSearchArithmetic
import Mathlib.Tactic

/-!
# Exact boolean-vector effects when visiting a search column

Marking the current column inserts one candidate, preserves every other flag,
restricts the prior slack invariant to the remaining unused targets, and
maintains nonzero matched-row pointers. No program-result property is assumed.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentVisitColumn

open AssignmentScanInvariant AssignmentAdjustmentInvariant AssignmentSearchCapacity AssignmentScanCut

/-- A target still unused after the physical write was previously unused and
is distinct from the just-visited column. -/
theorem unused_before (used : alloc.vec.Vec Bool) (column : Usize) (target : Nat)
    (hc : column.val < used.length) (ht : target < used.length)
    (hfalse : (used.set column true).val[target]! = false) : target ≠ column.val ∧ used.val[target]! = false := by
  by_cases he : target = column.val
  · subst target
    rw [vec_set_self used column true hc] at hfalse
    exact Bool.noConfusion hfalse
  · exact ⟨he,by simpa only [vec_set_other used column true target ht (Ne.symm he)] using hfalse⟩

/-- Every nonzero pointer, including the reserved fresh row, names a real row
while an unfinished assignment is being extended. -/
theorem nonzero_pointer_bounds (matched : Slice Usize) (n : Usize) (filled col : Nat)
    (hpartial : Assignment.PartialRows n.val filled (fun index => matched.val[index]!.val))
    (hroot : matched.val[0]!.val = filled+1) (hfilled : filled < n.val)
    (hcol : col ≤ n.val) (hnonzero : matched.val[col]!.val ≠ 0) :
    0 < matched.val[col]!.val ∧ matched.val[col]!.val ≤ n.val := by
  refine ⟨by omega,?_⟩
  by_cases hz : col = 0
  · rw [hz,hroot]
    omega
  · exact (hpartial.bound col (by omega) hcol).trans (Nat.le_of_lt hfilled)

theorem mark_matched (matched : Slice Usize) (used : alloc.vec.Vec Bool) (n column : Usize)
    (hlen : n.val < used.length) (_hcolumn : column.val ≤ n.val)
    (hused : UsedMatched matched (alloc.vec.Vec.deref used) n) (hrow : matched.val[column.val]!.val ≠ 0) :
    UsedMatched matched (alloc.vec.Vec.deref (used.set column true)) n := by
  intro target ht hf
  simp only [alloc.vec.Vec.deref,Slice.from_val] at hf
  by_cases he : target = column.val
  · simpa only [he] using hrow
  · have hi : target < used.length := lt_of_le_of_lt ht hlen
    rw [vec_set_other used column true target hi (Ne.symm he)] at hf
    exact hused target ht (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hf)

/-- The physical mark does not alter old slack values or predecessors; every
remaining unused target retains its earlier candidate minimum. -/
theorem mark_slackInvariant (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (matched : Slice Usize)
    (used : alloc.vec.Vec Bool) (candidates : Finset Nat) (slack : alloc.vec.Vec (Option I128))
    (predecessor : alloc.vec.Vec Usize) (n column : Usize)
    (hlen : n.val < used.length) (hcolumn : column.val ≤ n.val)
    (hinvariant : SlackInvariant cost u v matched (alloc.vec.Vec.deref used) candidates slack predecessor n) :
    SlackInvariant cost u v matched (alloc.vec.Vec.deref (used.set column true)) candidates slack predecessor n := by
  intro target hp hb hf
  simp only [alloc.vec.Vec.deref,Slice.from_val] at hf
  have hold := unused_before used column target (lt_of_le_of_lt hcolumn hlen) (lt_of_le_of_lt hb hlen) hf
  exact hinvariant target hp hb (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hold.2)

/-- Marking an unused current column increments the exact mathematical visit
count by one, matching the actual scalar increment. -/
theorem mark_cardinality (used : alloc.vec.Vec Bool) (n column : Usize)
    (hlen : n.val < used.length) (hcolumn : column.val ≤ n.val) (hnew : used.val[column.val]! = false) :
    (usedIndices (alloc.vec.Vec.deref (used.set column true)) (n.val+1)).card =
      (usedIndices (alloc.vec.Vec.deref used) (n.val+1)).card+1 := by
  rw [usedIndices_set_true used n column hcolumn hlen]
  apply Finset.card_insert_of_notMem
  intro hm
  have hh := (mem_usedIndices (alloc.vec.Vec.deref used) _ _).mp hm
  simp only [alloc.vec.Vec.deref,Slice.from_val,hnew] at hh
  exact Bool.noConfusion hh.2

/-- The first visit marks zero; all later visits preserve that reserved flag. -/
theorem mark_reserved (used : alloc.vec.Vec Bool) (n column : Usize)
    (hlen : n.val < used.length) (hcolumn : column.val ≤ n.val)
    (hreserved : used.val[0]! = true ∨ column.val = 0) : (used.set column true).val[0]! = true := by
  by_cases hz : column.val = 0
  · have he : column = 0#usize := by scalar_tac
    subst column
    exact vec_set_self used 0#usize true (by have h := hlen; scalar_tac)
  · rw [vec_set_other used column true 0 (by omega) hz]
    exact hreserved.resolve_right hz

end SubtreeProofs.Rust.AssignmentVisitColumn

end
