module

public import SubtreeProofs.Paper2004.PaperContainment
import Mathlib.Tactic

/-!
# A counterexample to the literal recursive containment definition

The printed Definition 2 of Lozano--Valiente (2004) describes a relation
whose recursive clause deletes a *top-level* matching pair, allowing its
three balanced pieces to shrink recursively. That clause does not permit
contracting only an edge strictly inside a tree whose root has one child.

This file proves a general one-edge characterization of the printed relation
and then proves the smallest discrepancy against operational contractions.
The contraction itself was already proved in `PaperContainment.lean`.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004
namespace OrderedTree

/-- A printed containment of exactly one pair less must have a witness
that deletes a top-level pair and otherwise leaves its three pieces fixed. -/
theorem PrintedContains.one_pair_drop_top_level
    {small large : DyckWord} (h : PrintedContains small large)
    (hLength : small.semilength + 1 = large.semilength) :
    ∃ leftWords middle rightWords : DyckWord,
      small = leftWords + middle + rightWords ∧
      large = leftWords + middle.nest + rightWords := by
  cases h with
  | refl word => omega
  | remove s1 s2 s3 t1 t2 t3 h1 h2 h3 =>
      have hle1 := PrintedContains.semilength_le h1
      have hle2 := PrintedContains.semilength_le h2
      have hle3 := PrintedContains.semilength_le h3
      simp only [DyckWord.semilength_add, DyckWord.semilength_nest] at hLength
      have heq1 : s1.semilength = t1.semilength := by omega
      have heq2 : s2.semilength = t2.semilength := by omega
      have heq3 : s3.semilength = t3.semilength := by omega
      have h1' := PrintedContains.eq_of_semilength_eq h1 heq1
      have h2' := PrintedContains.eq_of_semilength_eq h2 heq2
      have h3' := PrintedContains.eq_of_semilength_eq h3 heq3
      refine ⟨t1, t2, t3, ?_, rfl⟩
      simp only [h1', h2', h3']

/-- A Dyck word of semilength zero is empty. -/
theorem dyckWord_eq_zero_of_semilength_zero (word : DyckWord)
    (h : word.semilength = 0) : word = 0 := by
  have hCount := DyckWord.two_mul_semilength_eq_length (p := word)
  have hNil : (word : List DyckStep).length = 0 := by omega
  exact DyckWord.toList_eq_nil.mp (List.length_eq_zero_iff.mp hNil)

/-- A single nested word has exactly one top-level matching pair.
Any decomposition into a balanced prefix, one nested word, and a balanced
suffix therefore has empty prefix and suffix. -/
theorem nested_unique_top_level_decomposition
    (inside leftWords middle rightWords : DyckWord)
    (h : inside.nest = leftWords + middle.nest + rightWords) :
    leftWords = 0 ∧ middle = inside ∧ rightWords = 0 := by
  have hSize := congrArg DyckWord.semilength h
  simp only [DyckWord.semilength_add, DyckWord.semilength_nest] at hSize
  have hLeft : leftWords = 0 := by
    by_contra hNonempty
    have h' : inside.nest = leftWords + (middle.nest + rightWords) := by
      simpa only [add_assoc] using h
    have hFirst := congrArg DyckWord.firstReturn h'
    simp only [DyckWord.firstReturn_nest, DyckWord.firstReturn_add,
      if_neg hNonempty] at hFirst
    have hBound := DyckWord.firstReturn_lt_length hNonempty
    have hLeftCount := DyckWord.two_mul_semilength_eq_length (p := leftWords)
    have hInsideCount := DyckWord.two_mul_semilength_eq_length (p := inside)
    omega
  have hSize0 : inside.semilength + 1 =
      (middle.semilength + 1) + rightWords.semilength := by
    simpa [hLeft] using hSize
  have hReduced : inside.nest = middle.nest + rightWords := by
    simpa [hLeft] using h
  have hFirst := congrArg DyckWord.firstReturn hReduced
  have hNonzero : middle.nest ≠ 0 := DyckWord.nest_ne_zero
  simp only [DyckWord.firstReturn_nest, DyckWord.firstReturn_add,
    if_neg hNonzero] at hFirst
  have hInsideCount := DyckWord.two_mul_semilength_eq_length (p := inside)
  have hMiddleCount := DyckWord.two_mul_semilength_eq_length (p := middle)
  have hRightSize : rightWords.semilength = 0 := by omega
  have hRight := dyckWord_eq_zero_of_semilength_zero rightWords hRightSize
  have hNest : inside.nest = middle.nest := by simpa [hRight] using hReduced
  have hInsidePart := congrArg DyckWord.insidePart hNest
  have hMiddle : middle = inside := by
    simpa only [DyckWord.insidePart_nest] using hInsidePart.symm
  exact ⟨hLeft, hMiddle, hRight⟩

/-- When the larger word consists of one nested pair, a printed one-pair
deletion can only remove that outer pair. -/
theorem PrintedContains.one_pair_drop_nested
    {small inside : DyckWord}
    (h : PrintedContains small inside.nest)
    (hLength : small.semilength + 1 = inside.nest.semilength) :
    small = inside := by
  obtain ⟨leftWords, middle, rightWords, hSmall, hLarge⟩ :=
    PrintedContains.one_pair_drop_top_level h hLength
  obtain ⟨hl, hm, hr⟩ :=
    nested_unique_top_level_decomposition inside leftWords middle rightWords
      hLarge
  simpa [hl, hm, hr] using hSmall

/-- The operationally valid contraction `001011 → 0011` is not admitted
by the least relation generated by the printed Definition 2. -/
theorem branching_example_not_printed :
    ¬ PrintedContains
      (encodeDyck (.node [.node [singleton]]))
      (encodeDyck (.node [.node [singleton, singleton]])) := by
  intro h
  have hLength :
      (encodeDyck (.node [.node [singleton]])).semilength + 1 =
        (encodeDyck (.node [.node [singleton, singleton]])).semilength := by
    simp only [encodeDyck_semilength]
    decide
  have hNested :
      encodeDyck (.node [.node [singleton, singleton]]) =
        (encodeDyck (.node [singleton, singleton])).nest := by
    rfl
  rw [hNested] at h hLength
  have hEq := PrintedContains.one_pair_drop_nested h hLength
  have hNe :
      encodeDyck (.node [.node [singleton]]) ≠
        encodeDyck (.node [singleton, singleton]) := by
    decide
  exact hNe hEq

/-- Dyck contraction closure cannot increase the number of pairs. -/
theorem dyckEmbeds_semilength_le {small large : DyckWord}
    (h : DyckEmbeds small large) :
    small.semilength ≤ large.semilength := by
  unfold DyckEmbeds at h
  induction h with
  | refl => exact Nat.le_refl _
  | tail hprefix hstep ih =>
      have hStrict := dyckContractStep_semilength hstep
      omega

/-- On the smallest counterexample, every common word for the literal
printed relation has at most one pair, although the operational relation
admits the entire two-pair smaller tree. -/
theorem branching_example_printed_common_at_most_one
    (candidate : DyckWord)
    (hSmall : PrintedContains candidate
      (encodeDyck (.node [.node [singleton]])))
    (hLarge : PrintedContains candidate
      (encodeDyck (.node [.node [singleton, singleton]]))) :
    candidate.semilength ≤ 1 := by
  have hLE := PrintedContains.semilength_le hSmall
  have hSmallLength :
      (encodeDyck (.node [.node [singleton]])).semilength = 2 := by
    simp only [encodeDyck_semilength]
    decide
  by_contra hNot
  have hEqual :
      candidate.semilength =
        (encodeDyck (.node [.node [singleton]])).semilength := by
    omega
  have hCandidate := PrintedContains.eq_of_semilength_eq hSmall hEqual
  rw [hCandidate] at hLarge
  exact branching_example_not_printed hLarge

/-- The full two-pair tree is a common operational embedding in this example. -/
theorem branching_example_operational_common :
    DyckEmbeds
      (encodeDyck (.node [.node [singleton]]))
      (encodeDyck (.node [.node [singleton]])) ∧
    DyckEmbeds
      (encodeDyck (.node [.node [singleton]]))
      (encodeDyck (.node [.node [singleton, singleton]])) := by
  exact ⟨Relation.ReflTransGen.refl, branching_example_dyckEmbeds⟩

/-- That operational common embedding attains the maximum possible size:
no common sequence can exceed the smaller input's semilength. -/
theorem branching_example_operational_common_optimal
    (candidate : DyckWord)
    (hSmall : DyckEmbeds candidate
      (encodeDyck (.node [.node [singleton]]))) :
    candidate.semilength ≤
      (encodeDyck (.node [.node [singleton]])).semilength :=
  dyckEmbeds_semilength_le hSmall

/-- Operational pair deletion is strictly more permissive than the
least relation generated by the printed recursive Definition 2. -/
theorem printed_containment_not_complete :
    ¬ (∀ small large : DyckWord,
      DyckEmbeds small large → PrintedContains small large) := by
  intro h
  exact branching_example_not_printed
    (h _ _ branching_example_dyckEmbeds)

end OrderedTree
end SubtreeProofs.Paper2004

end
