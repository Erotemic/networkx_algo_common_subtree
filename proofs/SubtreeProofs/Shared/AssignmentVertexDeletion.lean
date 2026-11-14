module

public import SubtreeProofs.Shared.WeightedMatching
import Mathlib.Tactic

/-!
# Perfect assignment after deleting one vertex from each side

Removing row `a` and column `b` retains all original assignment edges except
those incident to either removed endpoint. If they were paired together, the
remaining assignment is already perfect. Otherwise exactly two edges are
removed: the unique surviving unmatched row is the old preimage of `b`, and
the unique surviving unmatched column is the old image of `a`.

This is the one-missing-edge combinatorial step of 2016 Lemma 6, independent
of the later augmenting-path algorithm and its cost model.
-/

@[expose] public section

namespace SubtreeProofs.AssignmentVertexDeletion

variable {A K : Type*} [Fintype A] [DecidableEq A]

/-- Surviving assigned rows, preserving original vertex identities. -/
def remainingRows (assignment : Equiv.Perm A) (removedRow removedColumn : A) : Finset A :=
  (Finset.univ.erase removedRow).erase (assignment.symm removedColumn)

/-- Retain exactly original assignment edges with both endpoints present. -/
def remainingPairs (assignment : Equiv.Perm A) (removedRow removedColumn : A) : Finset (A × A) :=
  (remainingRows assignment removedRow removedColumn).image (fun row => (row,assignment row))

@[simp] theorem mem_remainingRows (assignment : Equiv.Perm A) (removedRow removedColumn row : A) :
    row ∈ remainingRows assignment removedRow removedColumn ↔ row ≠ removedRow ∧ assignment row ≠ removedColumn := by
  simp only [remainingRows,Finset.mem_erase,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨hn,hrow⟩
    refine ⟨hrow,?_⟩
    intro he
    exact hn ((Equiv.eq_symm_apply assignment).mpr he)
  · rintro ⟨hrow,hcolumn⟩
    refine ⟨?_,hrow⟩
    intro he
    exact hcolumn ((Equiv.eq_symm_apply assignment).mp he)

@[simp] theorem mem_remainingPairs (assignment : Equiv.Perm A) (removedRow removedColumn row column : A) :
    (row,column) ∈ remainingPairs assignment removedRow removedColumn ↔
      row ≠ removedRow ∧ column ≠ removedColumn ∧ assignment row = column := by
  simp only [remainingPairs,Finset.mem_image,mem_remainingRows,Prod.mk.injEq]
  constructor
  · rintro ⟨other,⟨hr,hc⟩,he,hvalue⟩
    subst other
    exact ⟨hr,by simpa only [hvalue] using hc,hvalue⟩
  · rintro ⟨hr,hc,hvalue⟩
    exact ⟨row,⟨hr,by simpa only [hvalue] using hc⟩,rfl,hvalue⟩

theorem remainingPairs_card (assignment : Equiv.Perm A) (removedRow removedColumn : A) :
    (remainingPairs assignment removedRow removedColumn).card = (remainingRows assignment removedRow removedColumn).card := by
  apply Finset.card_image_iff.mpr
  intro row _ other _ he
  exact congrArg Prod.fst he

/-- When the deleted endpoints were paired together, exactly that edge is lost. -/
theorem remainingPairs_card_paired (assignment : Equiv.Perm A) (removedRow removedColumn : A)
    (hpaired : assignment removedRow = removedColumn) :
    (remainingPairs assignment removedRow removedColumn).card = Fintype.card A-1 := by
  rw [remainingPairs_card]
  have he : assignment.symm removedColumn = removedRow := (Equiv.symm_apply_eq assignment).mpr hpaired.symm
  simp only [remainingRows,he,Finset.erase_idem]
  exact Finset.card_erase_of_mem (Finset.mem_univ _)

/-- Otherwise precisely two old edges are lost; a surviving perfect assignment
has one more edge than this retained tight partial matching. -/
theorem remainingPairs_card_unpaired (assignment : Equiv.Perm A) (removedRow removedColumn : A)
    (hunpaired : assignment removedRow ≠ removedColumn) :
    (remainingPairs assignment removedRow removedColumn).card = Fintype.card A-2 := by
  rw [remainingPairs_card]
  have he : assignment.symm removedColumn ≠ removedRow := by
    intro he
    apply hunpaired
    rw [← he,Equiv.apply_symm_apply]
  have hm : assignment.symm removedColumn ∈ (Finset.univ : Finset A).erase removedRow :=
    Finset.mem_erase.mpr ⟨he,Finset.mem_univ _⟩
  rw [remainingRows,Finset.card_erase_of_mem hm,Finset.card_erase_of_mem (Finset.mem_univ removedRow)]
  rw [Finset.card_univ]
  omega

/-- Exact surviving-row coverage, including its unique possible deficit. -/
theorem row_unmatched_iff (assignment : Equiv.Perm A) (removedRow removedColumn row : A) (hr : row ≠ removedRow) :
    (¬ ∃ column, (row,column) ∈ remainingPairs assignment removedRow removedColumn) ↔ row = assignment.symm removedColumn := by
  constructor
  · intro hn
    apply (Equiv.eq_symm_apply assignment).mpr
    by_contra he
    exact hn ⟨assignment row,(mem_remainingPairs assignment removedRow removedColumn row (assignment row)).mpr ⟨hr,he,rfl⟩⟩
  · intro he
    rintro ⟨column,hpair⟩
    have hp := (mem_remainingPairs assignment removedRow removedColumn row column).mp hpair
    have hv : assignment row = removedColumn := (Equiv.eq_symm_apply assignment).mp he
    exact hp.2.1 (hp.2.2.symm.trans hv)

/-- Exact surviving-column coverage, including its unique possible deficit. -/
theorem column_unmatched_iff (assignment : Equiv.Perm A) (removedRow removedColumn column : A) (hc : column ≠ removedColumn) :
    (¬ ∃ row, (row,column) ∈ remainingPairs assignment removedRow removedColumn) ↔ column = assignment removedRow := by
  constructor
  · intro hn
    by_contra he
    have hr : assignment.symm column ≠ removedRow := by
      intro heq
      apply he
      rw [← heq,Equiv.apply_symm_apply]
    exact hn ⟨assignment.symm column,(mem_remainingPairs assignment removedRow removedColumn (assignment.symm column) column).mpr
      ⟨hr,hc,Equiv.apply_symm_apply _ _⟩⟩
  · intro he
    rintro ⟨row,hpair⟩
    have hp := (mem_remainingPairs assignment removedRow removedColumn row column).mp hpair
    exact hp.1 (assignment.injective (hp.2.2.trans he))

/-- Removing endpoints preserves independent compatible partial-matching
feasibility; both injectivity conditions follow from the original permutation. -/
theorem remainingPairs_valid (weights : A → A → Option K) (assignment : Equiv.Perm A)
    (hcompatible : ∀ row, weights row (assignment row) ≠ none) (removedRow removedColumn : A) :
    WeightedMatching.Valid weights (remainingPairs assignment removedRow removedColumn) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨row,column⟩ hp
    have he := (mem_remainingPairs assignment removedRow removedColumn row column).mp hp
    simpa only [he.2.2] using hcompatible row
  · rintro ⟨row,column⟩ hp ⟨other,target⟩ hq he
    have hp' := (mem_remainingPairs assignment removedRow removedColumn row column).mp hp
    have hq' := (mem_remainingPairs assignment removedRow removedColumn other target).mp hq
    apply Prod.ext he
    exact hp'.2.2.symm.trans ((congrArg assignment he).trans hq'.2.2)
  · rintro ⟨row,column⟩ hp ⟨other,target⟩ hq he
    have hp' := (mem_remainingPairs assignment removedRow removedColumn row column).mp hp
    have hq' := (mem_remainingPairs assignment removedRow removedColumn other target).mp hq
    apply Prod.ext _ he
    apply assignment.injective
    exact hp'.2.2.trans (he.trans hq'.2.2.symm)

/-- Deletion does not disturb tightness of any retained assignment edge. -/
theorem remainingPairs_tight [Add K] (matrix : A → A → K) (rows columns : A → K)
    (assignment : Equiv.Perm A) (htight : ∀ row, rows row + columns (assignment row) = matrix row (assignment row))
    (removedRow removedColumn : A) :
    ∀ pair ∈ remainingPairs assignment removedRow removedColumn, rows pair.1 + columns pair.2 = matrix pair.1 pair.2 := by
  rintro ⟨row,column⟩ hp
  have he := (mem_remainingPairs assignment removedRow removedColumn row column).mp hp
  simpa only [he.2.2] using htight row


/-- The induced surviving graph forbids every edge at either removed endpoint. -/
def deleteEndpoints (weights : A → A → Option K) (removedRow removedColumn : A) : A → A → Option K :=
  fun row column => if row = removedRow ∨ column = removedColumn then none else weights row column

/-- The retained partial matching is compatible in the actual induced graph,
not merely in the original graph before endpoint removal. -/
theorem remainingPairs_valid_deleted (weights : A → A → Option K) (assignment : Equiv.Perm A)
    (hcompatible : ∀ row, weights row (assignment row) ≠ none) (removedRow removedColumn : A) :
    WeightedMatching.Valid (deleteEndpoints weights removedRow removedColumn)
      (remainingPairs assignment removedRow removedColumn) := by
  have hv := remainingPairs_valid weights assignment hcompatible removedRow removedColumn
  refine ⟨?_,hv.2⟩
  rintro ⟨row,column⟩ hp
  have he := (mem_remainingPairs assignment removedRow removedColumn row column).mp hp
  have hn : ¬ (row = removedRow ∨ column = removedColumn) := not_or_intro he.1 he.2.1
  simpa only [deleteEndpoints,hn,↓reduceIte] using hv.1 (row,column) hp

/-- In the unpaired case the retained matching is exactly one edge short of
covering both surviving sides. This is a derived deficit, not a premise. -/
theorem one_pair_deficit (assignment : Equiv.Perm A) (removedRow removedColumn : A)
    (hunpaired : assignment removedRow ≠ removedColumn) :
    (remainingPairs assignment removedRow removedColumn).card+1 = Fintype.card A-1 := by
  have hd : assignment.symm removedColumn ≠ removedRow := by
    intro he
    apply hunpaired
    rw [← he,Equiv.apply_symm_apply]
  have hc : ({removedRow,assignment.symm removedColumn} : Finset A).card = 2 := by simp [hd,Ne.symm hd]
  have hb := Finset.card_le_univ ({removedRow,assignment.symm removedColumn} : Finset A)
  rw [hc] at hb
  rw [remainingPairs_card_unpaired assignment removedRow removedColumn hunpaired]
  omega

end SubtreeProofs.AssignmentVertexDeletion

end
