module

public import SubtreeProofs.Shared.AssignmentDualityOn
public import Mathlib.GroupTheory.Perm.List
import Mathlib.Tactic

/-! # Ranked predecessor paths and their cyclic assignment permutation -/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A : Type*} [DecidableEq A]

/-- Follow original matched columns backwards through predecessor rows until
the free root is reached. The list records original columns in search order. -/
inductive PredecessorTrace (assignment : Equiv.Perm A) (predecessor : A → A) (root : A) : A → List A → Prop
  | stop (column : A) (h : predecessor column = root) : PredecessorTrace assignment predecessor root column [column]
  | step (column : A) (rest : List A) (h : predecessor column ≠ root)
      (tail : PredecessorTrace assignment predecessor root (assignment (predecessor column)) (assignment (predecessor column)::rest)) :
      PredecessorTrace assignment predecessor root column (column::assignment (predecessor column)::rest)

/-- Strictly decreasing positive predecessor ranks construct a finite simple
trace. No path or acyclicity certificate is assumed separately. -/
theorem exists_ranked_predecessor_trace (assignment : Equiv.Perm A) (predecessor : A → A) (root : A) (rank : A → Nat)
    (hRank : ∀ column, 0 < rank column → predecessor column = root ∨
      0 < rank (assignment (predecessor column)) ∧ rank (assignment (predecessor column)) < rank column)
    (start : A) (hStart : 0 < rank start) :
    ∃ rest, PredecessorTrace assignment predecessor root start (start::rest) ∧ (start::rest).Nodup ∧
      ∀ column ∈ start::rest, 0 < rank column ∧ rank column ≤ rank start := by
  generalize hn : rank start = n at *
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    have hStartRank : 0 < rank start := by omega
    rcases hRank start hStartRank with hStop | ⟨hPositive,hLess⟩
    · refine ⟨[],.stop start hStop,by simp,?_⟩
      intro column hc
      have he : column = start := by simpa only [List.mem_singleton] using hc
      subst column
      exact ⟨hStartRank,by omega⟩
    · by_cases hStop : predecessor start = root
      · refine ⟨[],.stop start hStop,by simp,?_⟩
        intro column hc
        have he : column = start := by simpa only [List.mem_singleton] using hc
        subst column
        exact ⟨hStartRank,by omega⟩
      · obtain ⟨rest,hTrace,hNodup,hBounds⟩ := ih (rank (assignment (predecessor start))) (by omega)
          (assignment (predecessor start)) rfl hPositive
        have hFresh : start ∉ assignment (predecessor start)::rest := by
          intro hm
          have hh := (hBounds start hm).2
          omega
        refine ⟨assignment (predecessor start)::rest,.step start rest hStop hTrace,List.nodup_cons.mpr ⟨hFresh,hNodup⟩,?_⟩
        intro column hc
        rcases List.mem_cons.mp hc with he | he
        · subst column
          exact ⟨hStartRank,by omega⟩
        · have hh := hBounds column he
          exact ⟨hh.1,by omega⟩

/-- The trace's successor is the predecessor row's original matched column;
its last column instead has the free root as predecessor. -/
theorem PredecessorTrace.at (assignment : Equiv.Perm A) (predecessor : A → A) (root : A)
    {start : A} {path : List A} (h : PredecessorTrace assignment predecessor root start path) :
    ∀ index (hi : index < path.length),
      if hn : index+1 < path.length then predecessor path[index] ≠ root ∧ path[index+1] = assignment (predecessor path[index])
      else predecessor path[index] = root := by
  induction h with
  | stop column hStop =>
    intro index hi
    have he : index = 0 := by simp only [List.length_singleton] at hi; omega
    subst index
    simpa only [List.length_singleton,lt_self_iff_false,↓reduceDIte,List.getElem_cons_zero] using hStop
  | step column rest hNot hTail ih =>
    intro index hi
    cases index with
    | zero =>
      simp only [List.length_cons,Nat.zero_add,List.getElem_cons_zero,List.getElem_cons_succ]
      rw [dite_eq_left (by omega)]
      exact ⟨hNot,True.intro⟩
    | succ index =>
      have hb : index < (assignment (predecessor column)::rest).length := by simp only [List.length_cons] at hi ⊢; omega
      simpa only [List.length_cons,List.getElem_cons_succ,Nat.succ_lt_succ_iff,Nat.succ_add] using ih index hb

/-- Mathlib's canonical list cycle sends each trace column to the old matched
column of its predecessor row, closing the final edge at the starting column. -/
theorem PredecessorTrace.formPerm (assignment : Equiv.Perm A) (predecessor : A → A) (root start : A) (rest : List A)
    (h : PredecessorTrace assignment predecessor root start (start::rest)) (hn : (start::rest).Nodup)
    (column : A) (hc : column ∈ start::rest) :
    (start::rest).formPerm column = if predecessor column = root then start else assignment (predecessor column) := by
  obtain ⟨index,hi,he⟩ := List.getElem_of_mem hc
  subst column
  have hh := h.at assignment predecessor root index hi
  by_cases hb : index+1 < (start::rest).length
  · rw [dite_eq_left hb] at hh
    rw [List.formPerm_apply_lt_getElem _ hn index hb,ite_eq_right hh.1]
    exact hh.2
  · rw [dite_eq_right hb] at hh
    rw [ite_eq_left hh,List.formPerm_apply_getElem _ hn index hi]
    have he : index+1 = (start::rest).length := by omega
    simp only [he,Nat.mod_self,List.getElem_cons_zero]

end SubtreeProofs.Assignment

end
