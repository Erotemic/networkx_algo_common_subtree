module

public import SubtreeProofs.Shared.AssignmentAugmentation
import Mathlib.Tactic

/-!
# Free columns and finite search capacity of partial assignments

These are independent counting consequences of row coverage and injectivity.
They justify availability of a free column and the visit-counter bound in an
alternating-tree search with the fresh row stored at reserved column zero.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

def matchedColumns (n : Nat) (pointers : Nat → Nat) : Finset Nat :=
  (Finset.Icc 1 n).filter (fun col => pointers col ≠ 0)

@[simp] theorem mem_matchedColumns (n : Nat) (pointers : Nat → Nat) (col : Nat) :
    col ∈ matchedColumns n pointers ↔ 0 < col ∧ col ≤ n ∧ pointers col ≠ 0 := by
  simp only [matchedColumns,Finset.mem_filter,Finset.mem_Icc]
  omega

theorem PartialRows.matched_image {n filled : Nat} {pointers : Nat → Nat} (h : PartialRows n filled pointers) :
    (matchedColumns n pointers).image pointers = Finset.Icc 1 filled := by
  ext row
  constructor
  · intro hm
    obtain ⟨col,hcol,he⟩ := Finset.mem_image.mp hm
    obtain ⟨hp,hb,hn⟩ := (mem_matchedColumns n pointers col).mp hcol
    have hle := h.bound col hp hb
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro hm
    obtain ⟨hp,hb⟩ := Finset.mem_Icc.mp hm
    obtain ⟨col,hcp,hcb,he⟩ := h.complete row hp hb
    exact Finset.mem_image.mpr ⟨col,(mem_matchedColumns n pointers col).mpr ⟨hcp,hcb,by omega⟩,he⟩

theorem PartialRows.matched_card {n filled : Nat} {pointers : Nat → Nat} (h : PartialRows n filled pointers) :
    (matchedColumns n pointers).card = filled := by
  have hi : Set.InjOn pointers (matchedColumns n pointers) := by
    intro first hf second hs he
    obtain ⟨hfp,hfb,hfn⟩ := (mem_matchedColumns n pointers first).mp hf
    obtain ⟨hsp,hsb,_⟩ := (mem_matchedColumns n pointers second).mp hs
    exact h.injective first hfp hfb hfn second hsp hsb he
  have hc := Finset.card_image_of_injOn hi
  rw [h.matched_image,Nat.card_Icc] at hc
  omega

/-- Before every row is matched, an actual real column remains free. -/
theorem PartialRows.exists_unmatched {n filled : Nat} {pointers : Nat → Nat}
    (h : PartialRows n filled pointers) (hunfinished : filled < n) :
    ∃ col, 0 < col ∧ col ≤ n ∧ pointers col = 0 := by
  have hc : (matchedColumns n pointers).card < (Finset.Icc 1 n).card := by
    rw [h.matched_card,Nat.card_Icc]
    omega
  obtain ⟨col,hcol,hfree⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hb := Finset.mem_Icc.mp hcol
  refine ⟨col,hb.1,hb.2,?_⟩
  by_contra hn
  exact hfree ((mem_matchedColumns n pointers col).mpr ⟨hb.1,hb.2,hn⟩)

/-- The fresh row at zero remains distinct from every earlier nonzero row
pointer, extending injectivity to the reserved column. -/
theorem PartialRows.with_root_injective {n filled : Nat} {pointers : Nat → Nat}
    (h : PartialRows n filled pointers) (hroot : pointers 0 = filled+1)
    (first : Nat) (hf : first ≤ n) (hfn : pointers first ≠ 0)
    (second : Nat) (hs : second ≤ n) (he : pointers first = pointers second) : first = second := by
  by_cases hf0 : first = 0 <;> by_cases hs0 : second = 0
  · omega
  · have hle := h.bound second (by omega) hs
    rw [hf0,hroot] at he
    omega
  · have hle := h.bound first (by omega) hf
    rw [hs0,hroot] at he
    omega
  · exact h.injective first (by omega) hf hfn second (by omega) hs he

/-- At most one distinct positive row pointer can be visited per processed
row or fresh row, including reserved column zero. -/
theorem PartialRows.used_card_le {n filled : Nat} {pointers : Nat → Nat}
    (h : PartialRows n filled pointers) (hroot : pointers 0 = filled+1) (used : Finset Nat)
    (hused : ∀ col ∈ used, col ≤ n ∧ pointers col ≠ 0) : used.card ≤ filled+1 := by
  have hi : Set.InjOn pointers used := by
    intro first hf second hs he
    exact h.with_root_injective hroot first (hused first hf).1 (hused first hf).2 second (hused second hs).1 he
  have hsub : used.image pointers ⊆ Finset.Icc 1 (filled+1) := by
    intro row hr
    obtain ⟨col,hcol,he⟩ := Finset.mem_image.mp hr
    have hc := hused col hcol
    apply Finset.mem_Icc.mpr
    refine ⟨by omega,?_⟩
    by_cases hz : col = 0
    · rw [hz,hroot] at he
      omega
    · have hb := h.bound col (by omega) hc.1
      omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hi,Nat.card_Icc] at hc
  omega

/-- A further unvisited column carrying a row proves the current visit count
is strictly below n, exactly the source guard's required direction. -/
theorem PartialRows.used_card_lt {n filled : Nat} {pointers : Nat → Nat}
    (h : PartialRows n filled pointers) (hroot : pointers 0 = filled+1) (hfilled : filled < n)
    (used : Finset Nat) (hused : ∀ col ∈ used, col ≤ n ∧ pointers col ≠ 0)
    (column : Nat) (hcolumn : column ≤ n) (hrow : pointers column ≠ 0) (hnew : column ∉ used) : used.card < n := by
  have hb := h.used_card_le hroot (insert column used) (by
    intro col hc
    rcases Finset.mem_insert.mp hc with he | hm
    · subst col
      exact ⟨hcolumn,hrow⟩
    · exact hused col hm)
  rw [Finset.card_insert_of_notMem hnew] at hb
  omega

end SubtreeProofs.Assignment

end
