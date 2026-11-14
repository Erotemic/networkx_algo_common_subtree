module

public import SubtreeProofs.Shared.AssignmentDuality
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Independent partial assignments represented by row pointers

Zero denotes an unmatched column. Positive columns and rows are one based;
reserved input slot zero may carry the fresh row during augmentation.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

/-- Real column pointers form an injective assignment covering exactly the
first `filled` positive rows. Zero is allowed at any unmatched column. -/
structure PartialRows (n filled : Nat) (pointers : Nat → Nat) : Prop where
  bound : ∀ col, 0 < col → col ≤ n → pointers col ≤ filled
  injective : ∀ first, 0 < first → first ≤ n → pointers first ≠ 0 →
    ∀ second, 0 < second → second ≤ n → pointers first = pointers second → first = second
  complete : ∀ row, 0 < row → row ≤ filled → ∃ col, 0 < col ∧ col ≤ n ∧ pointers col = row

theorem partialRows_zero (n : Nat) : PartialRows n 0 (fun _ => 0) := by
  refine ⟨by simp,by simp,?_⟩
  intro row hp hb
  omega

theorem PartialRows.congr {n filled : Nat} {first second : Nat → Nat} (h : PartialRows n filled first)
    (heq : ∀ col, 0 < col → col ≤ n → first col = second col) : PartialRows n filled second := by
  refine ⟨?_,?_,?_⟩
  · intro col hp hb
    rw [← heq col hp hb]
    exact h.bound col hp hb
  · intro firstCol hfp hfb hnonzero secondCol hsp hsb he
    rw [← heq firstCol hfp hfb] at hnonzero
    rw [← heq firstCol hfp hfb, ← heq secondCol hsp hsb] at he
    exact h.injective firstCol hfp hfb hnonzero secondCol hsp hsb he
  · intro row hp hb
    obtain ⟨col,hcp,hcb,he⟩ := h.complete row hp hb
    exact ⟨col,hcp,hcb,(heq col hcp hcb).symm.trans he⟩

/-- A bijective rerouting from real columns to the old columns with an
unmatched terminal replaced by reserved column zero adds exactly the fresh
row, preserving all earlier assignments' coverage and injectivity. -/
theorem reassign_preserves_partial (n filled terminal : Nat) (pointers route : Nat → Nat)
    (hpartial : PartialRows n filled pointers) (hroot : pointers 0 = filled+1) (hterminal : pointers terminal = 0)
    (hbound : ∀ col, 0 < col → col ≤ n → route col ≤ n ∧ route col ≠ terminal)
    (hinjective : Set.InjOn route (Finset.Icc 1 n))
    (hsurjective : ∀ original, original ≤ n → original ≠ terminal →
      ∃ col, 0 < col ∧ col ≤ n ∧ route col = original) :
    PartialRows n (filled+1) (fun col => pointers (route col)) := by
  refine ⟨?_,?_,?_⟩
  · intro col hp hb
    have hr := hbound col hp hb
    by_cases hz : route col = 0
    · rw [hz,hroot]
    · have hle := hpartial.bound (route col) (by omega) hr.1
      omega
  · intro first hfp hfb hnonzero second hsp hsb he
    have hf := hbound first hfp hfb
    have hs := hbound second hsp hsb
    apply hinjective (Finset.mem_Icc.mpr ⟨hfp,hfb⟩) (Finset.mem_Icc.mpr ⟨hsp,hsb⟩)
    by_cases hfzero : route first = 0 <;> by_cases hszero : route second = 0
    · omega
    · have hle := hpartial.bound (route second) (by omega) hs.1
      rw [hfzero,hroot] at he
      omega
    · have hle := hpartial.bound (route first) (by omega) hf.1
      rw [hszero,hroot] at he
      omega
    · exact hpartial.injective (route first) (by omega) hf.1 hnonzero (route second) (by omega) hs.1 he
  · intro row hp hb
    by_cases he : row = filled+1
    · have hrootNonterminal : 0 ≠ terminal := by
        intro hz
        rw [← hz,hroot] at hterminal
        omega
      obtain ⟨col,hcp,hcb,hroute⟩ := hsurjective 0 (by omega) hrootNonterminal
      exact ⟨col,hcp,hcb,by rw [hroute,hroot,he]⟩
    · have hr : row ≤ filled := by omega
      obtain ⟨original,hop,hob,hpointer⟩ := hpartial.complete row hp hr
      have hne : original ≠ terminal := by
        intro heq
        rw [heq,hterminal] at hpointer
        omega
      obtain ⟨col,hcp,hcb,hroute⟩ := hsurjective original hob hne
      exact ⟨col,hcp,hcb,by rw [hroute,hpointer]⟩


/-- Every currently matched real column is tight for the independent matrix
and potential functions. Unmatched columns impose no equality. -/
def TightPointers {K : Type*} [Add K] (n : Nat) (matrix : Nat → Nat → K) (rows columns : Nat → K)
    (pointers : Nat → Nat) : Prop :=
  ∀ col, 0 < col → col ≤ n → pointers col ≠ 0 → rows (pointers col) + columns col = matrix (pointers col) col

theorem TightPointers.congr {K : Type*} [Add K] {n : Nat} {matrix : Nat → Nat → K} {rows columns : Nat → K}
    {first second : Nat → Nat} (h : TightPointers n matrix rows columns first)
    (heq : ∀ col, 0 < col → col ≤ n → first col = second col) : TightPointers n matrix rows columns second := by
  intro col hp hb hn
  rw [← heq col hp hb] at hn ⊢
  exact h col hp hb hn

end SubtreeProofs.Assignment

end
