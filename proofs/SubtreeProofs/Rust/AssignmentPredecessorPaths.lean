module

public import SubtreeProofs.Rust.AssignmentAugmentation
import Mathlib.Tactic

/-!
# Ranked predecessor forests yield valid finite augmentation paths

The alternating-tree search can assign discovery ranks to predecessor links.
Strict descent rules out cycles and yields a simple path to the reserved
column zero. This connects a local forest invariant to actual Rust execution.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentPredecessorPaths

open AssignmentAugmentation AssignmentAdjustmentInvariant

/-- Local predecessor-forest conditions, independent of the augmentation
program and its result. Zero is the only vertex exempt from strict descent. -/
def Ranked (predecessor : Slice Usize) (n : Usize) (vertices : Finset Nat) (rank : Nat → Nat) : Prop :=
  (∀ col ∈ vertices, col ≤ n.val) ∧
    ∀ col ∈ vertices, col ≠ 0 → predecessor.val[col]!.val ∈ vertices ∧
      rank predecessor.val[col]!.val < rank col

/-- Strictly descending predecessor links construct a simple path. Every
path entry also has rank at most that of its starting column. -/
theorem exists_validPath (predecessor : Slice Usize) (n : Usize) (vertices : Finset Nat) (rank : Nat → Nat)
    (hranked : Ranked predecessor n vertices rank) (col : Nat) (hcol : col ∈ vertices) :
    ∃ path, ValidPath predecessor n path ∧ path.headD 0 = col ∧
      ∀ entry ∈ path, entry ∈ vertices ∧ rank entry ≤ rank col := by
  induction col using (measure rank).wf.induction with
  | h col ih =>
    by_cases hz : col = 0
    · subst col
      exact ⟨[],⟨by simp,by simp,by trivial⟩,rfl,by simp⟩
    · have hnext := hranked.2 col hcol hz
      obtain ⟨rest,hrest,hhead,hranks⟩ := ih predecessor.val[col]!.val hnext.2 hnext.1
      have hnot : col ∉ rest := by
        intro hm
        have hle := (hranks col hm).2
        omega
      refine ⟨col::rest,⟨List.nodup_cons.mpr ⟨hnot,hrest.1⟩,?_,?_,?_⟩,rfl,?_⟩
      · intro entry hentry
        rcases List.mem_cons.mp hentry with he | hm
        · subst entry
          exact ⟨by omega,hranked.1 col hcol⟩
        · exact hrest.2.1 entry hm
      · exact hhead.symm
      · exact hrest.2.2
      · intro entry hentry
        rcases List.mem_cons.mp hentry with he | hm
        · subst entry
          exact ⟨hcol,le_rfl⟩
        · exact ⟨(hranks entry hm).1, (hranks entry hm).2.trans (Nat.le_of_lt hnext.2)⟩

/-- Local forest ranks suffice for successful actual augmentation; a path or
an algorithm-output certificate need not be supplied by the caller. -/
theorem augment_matching_ranked_spec (matched : alloc.vec.Vec Usize) (predecessor : Slice Usize)
    (column n : Usize) (vertices : Finset Nat) (rank : Nat → Nat)
    (hranked : Ranked predecessor n vertices rank) (hcol : column.val ∈ vertices)
    (hmatched : n.val < matched.length) (hpred : n.val < predecessor.length) :
    augment_matching matched predecessor column n ⦃ output =>
      output.1 = core.result.Result.Ok () ∧ ∃ path,
        ValidPath predecessor n path ∧ path.headD 0 = column.val ∧
          Frame matched output.2 id (shifted matched predecessor path) ⦄ := by
  obtain ⟨path,hvalid,hhead,_⟩ := exists_validPath predecessor n vertices rank hranked column.val hcol
  apply WP.spec_mono (augment_matching_spec matched predecessor column n path hvalid hhead.symm hmatched hpred)
  rintro output ⟨hsuccess,hframe⟩
  exact ⟨hsuccess,path,hvalid,hhead,hframe⟩

end SubtreeProofs.Rust.AssignmentPredecessorPaths

end
