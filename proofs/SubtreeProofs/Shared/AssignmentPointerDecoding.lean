module

public import SubtreeProofs.Shared.AssignmentAugmentation
import Mathlib.Tactic

/-!
# Complete row-pointer assignments decode to permutations

Surjective row coverage and nonzero-pointer injectivity force every real
column to be matched. A decoded inverse permutation then connects pointer
edge tightness to the independent finite assignment optimum.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

/-- A complete pointer matching has an inverse permutation of real indices. -/
theorem PartialRows.exists_permutation {n : Nat} {pointers : Nat → Nat} (h : PartialRows n n pointers) :
    ∃ assignment : Equiv.Perm (Fin n), ∀ row, pointers ((assignment row).val+1) = row.val+1 := by
  classical
  have hexists : ∀ row : Fin n, ∃ col : Fin n, pointers (col.val+1) = row.val+1 := by
    intro row
    obtain ⟨col,hp,hb,he⟩ := h.complete (row.val+1) (by omega) (by have hr := row.isLt; omega)
    refine ⟨⟨col-1,by omega⟩,?_⟩
    have hc : col-1+1 = col := by omega
    simpa only [hc] using he
  choose assignment hassignment using hexists
  have hi : Function.Injective assignment := by
    intro first second he
    have hf := hassignment first
    have hs := hassignment second
    rw [he] at hf
    apply Fin.ext
    omega
  exact ⟨Equiv.ofBijective assignment ⟨hi,(Finite.injective_iff_surjective).mp hi⟩,hassignment⟩

/-- At full row coverage, no real column can remain unmatched. -/
theorem PartialRows.full_positive {n : Nat} {pointers : Nat → Nat} (h : PartialRows n n pointers)
    (col : Nat) (hp : 0 < col) (hb : col ≤ n) : 0 < pointers col := by
  obtain ⟨assignment,hassignment⟩ := h.exists_permutation
  let index : Fin n := ⟨col-1,by omega⟩
  obtain ⟨row,hrow⟩ := assignment.surjective index
  have he := hassignment row
  have hc : (assignment row).val+1 = col := by rw [hrow]; dsimp only [index]; omega
  rw [hc] at he
  omega

/-- Pointer tightness for the decoded permutation is the standard finite
assignment tightness condition after changing to zero-based real indices. -/
theorem tight_of_inverse {K : Type*} [CommRing K] {n : Nat}
    (matrix : Nat → Nat → K) (rows columns : Nat → K) (pointers : Nat → Nat)
    (assignment : Equiv.Perm (Fin n))
    (hinverse : ∀ row, pointers ((assignment row).val+1) = row.val+1)
    (htight : TightPointers n matrix rows columns pointers) :
    Tight (fun row col : Fin n => matrix (row.val+1) (col.val+1))
      (fun row => rows (row.val+1)) (fun col => columns (col.val+1)) assignment := by
  intro row
  have hc : (assignment row).val+1 ≤ n := by have h := (assignment row).isLt; omega
  have hn : pointers ((assignment row).val+1) ≠ 0 := by rw [hinverse]; omega
  simpa only [hinverse] using htight ((assignment row).val+1) (by omega) hc hn

end SubtreeProofs.Assignment

end
