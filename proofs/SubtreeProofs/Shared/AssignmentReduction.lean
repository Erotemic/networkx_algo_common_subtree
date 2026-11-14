module

public import SubtreeProofs.Shared.WeightedMatching
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Partial matching and dummy assignment

A partial bijection extends to a permutation on `L ⊕ R`: each matched pair
swaps its endpoints, and unmatched endpoints stay fixed. This uses exactly
|L|+|R| rows and columns, with no forbidden-edge sentinel.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.AssignmentReduction

variable {L R : Type*}

noncomputable def leftPartner (pairs : Finset (L × R)) (l : L) : Option R := by
  classical
  exact if h : ∃ r, (l,r) ∈ pairs then some (Classical.choose h) else none

noncomputable def rightPartner (pairs : Finset (L × R)) (r : R) : Option L := by
  classical
  exact if h : ∃ l, (l,r) ∈ pairs then some (Classical.choose h) else none

theorem leftPartner_some {weights : L → R → Option ℝ} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) (l : L) (r : R) :
    leftPartner pairs l = some r ↔ (l,r) ∈ pairs := by
  classical
  unfold leftPartner
  split
  · rename_i h
    have hc := Classical.choose_spec h
    constructor
    · intro he; simpa only [Option.some.inj he] using hc
    · intro hp
      have he := hv.2.1 _ hc _ hp rfl
      exact congrArg some (congrArg Prod.snd he)
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro hp
    exact h ⟨r,hp⟩

theorem rightPartner_some {weights : L → R → Option ℝ} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) (l : L) (r : R) :
    rightPartner pairs r = some l ↔ (l,r) ∈ pairs := by
  classical
  unfold rightPartner
  split
  · rename_i h
    have hc := Classical.choose_spec h
    constructor
    · intro he; simpa only [Option.some.inj he] using hc
    · intro hp
      have he := hv.2.2 _ hc _ hp rfl
      exact congrArg some (congrArg Prod.fst he)
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro hp
    exact h ⟨l,hp⟩

noncomputable def swapPartners (pairs : Finset (L × R)) : L ⊕ R → L ⊕ R
  | .inl l => match leftPartner pairs l with
    | some r => .inr r
    | none => .inl l
  | .inr r => match rightPartner pairs r with
    | some l => .inl l
    | none => .inr r

theorem swapPartners_involutive {weights : L → R → Option ℝ} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) : Function.Involutive (swapPartners pairs) := by
  intro x
  cases x with
  | inl l =>
    cases h : leftPartner pairs l with
    | none => simp [swapPartners, h]
    | some r =>
      have hr := (rightPartner_some hv l r).mpr ((leftPartner_some hv l r).mp h)
      simp [swapPartners, h, hr]
  | inr r =>
    cases h : rightPartner pairs r with
    | none => simp [swapPartners, h]
    | some l =>
      have hl := (leftPartner_some hv l r).mpr ((rightPartner_some hv l r).mp h)
      simp [swapPartners, h, hl]

/-- A concrete perfect assignment containing every selected real-real pair. -/
noncomputable def extend {weights : L → R → Option ℝ} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) : Equiv.Perm (L ⊕ R) :=
  (swapPartners_involutive hv).toPerm

theorem extend_pair {weights : L → R → Option ℝ} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) {l : L} {r : R} (hp : (l,r) ∈ pairs) :
    extend hv (.inl l) = .inr r := by
  change swapPartners pairs (.inl l) = .inr r
  simp [swapPartners, (leftPartner_some hv l r).mpr hp]

/-- Forbidden/nonpositive real pairs and all dummy assignments have zero profit. -/
def profit (weights : L → R → Option ℝ) : L ⊕ R → L ⊕ R → ℝ
  | .inl l, .inr r => max 0 ((weights l r).getD 0)
  | _, _ => 0

variable [Fintype L] [Fintype R]

/-- A complete square assignment's profit. -/
def assignmentWeight (weights : L → R → Option ℝ) (σ : Equiv.Perm (L ⊕ R)) : ℝ :=
  ∑ x, profit weights x (σ x)

/-- Retain just strictly positive, compatible real-real assignments. -/
noncomputable def decode (weights : L → R → Option ℝ) (σ : Equiv.Perm (L ⊕ R)) : Finset (L × R) := by
  classical
  exact Finset.univ.filter (fun p => σ (.inl p.1) = .inr p.2 ∧ 0 < (weights p.1 p.2).getD 0)

@[simp] theorem mem_decode (weights : L → R → Option ℝ) (σ : Equiv.Perm (L ⊕ R))
    (p : L × R) : p ∈ decode weights σ ↔
      σ (.inl p.1) = .inr p.2 ∧ 0 < (weights p.1 p.2).getD 0 := by
  classical
  simp [decode]

theorem decode_valid (weights : L → R → Option ℝ) (σ : Equiv.Perm (L ⊕ R)) :
    Valid weights (decode weights σ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hn
    have hpos := ((mem_decode weights σ p).mp hp).2
    simp [hn] at hpos
  · intro p hp q hq hl
    apply Prod.ext hl
    have hp' := ((mem_decode weights σ p).mp hp).1
    have hq' := ((mem_decode weights σ q).mp hq).1
    rw [hl, hq'] at hp'
    exact Sum.inr.inj hp'.symm
  · intro p hp q hq hr
    apply Prod.ext _ hr
    have hp' := ((mem_decode weights σ p).mp hp).1
    have hq' := ((mem_decode weights σ q).mp hq).1
    rw [hr, ← hq'] at hp'
    exact Sum.inl.inj (σ.injective hp')

/-- Decoding preserves the complete assignment profit exactly. -/
theorem decode_weight (weights : L → R → Option ℝ) (σ : Equiv.Perm (L ⊕ R)) :
    weight weights (decode weights σ) = assignmentWeight weights σ := by
  classical
  let active := Finset.univ.filter (fun x => 0 < profit weights x (σ x))
  have hrestrict : assignmentWeight weights σ = ∑ x ∈ active, profit weights x (σ x) := by
    unfold assignmentWeight
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _ hx
    have hn : ¬ 0 < profit weights x (σ x) := by simpa [active] using hx
    have hp : 0 ≤ profit weights x (σ x) := by
      cases x with
      | inl l => cases σ (.inl l) <;> simp [profit]
      | inr r => simp [profit]
    exact le_antisymm (le_of_not_gt hn) hp
  rw [hrestrict]
  unfold weight
  apply Finset.sum_bij (fun p _ => Sum.inl p.1)
  · intro p hp
    have h := (mem_decode weights σ p).mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [h.1]
    exact lt_of_lt_of_le h.2 (le_max_right _ _)
  · intro p hp q hq he
    exact (decode_valid weights σ).2.1 p hp q hq (Sum.inl.inj he)
  · intro x hx
    have hpos : 0 < profit weights x (σ x) := (Finset.mem_filter.mp hx).2
    cases x with
    | inr r => simp [profit] at hpos
    | inl l =>
      cases he : σ (.inl l) with
      | inl l' => simp [he, profit] at hpos
      | inr r =>
        refine ⟨(l,r), (mem_decode weights σ (l,r)).mpr ⟨he, ?_⟩, rfl⟩
        simpa [he, profit] using hpos
  · intro p hp
    have h := (mem_decode weights σ p).mp hp
    simp [h.1, profit, max_eq_right (le_of_lt h.2)]

/-- Extension cannot lose weight: replacing a negative selected weight by
zero can only improve the objective. No sign or magnitude bound is needed. -/
theorem weight_le_extend {weights : L → R → Option ℝ} {pairs : Finset (L × R)}
    (hv : Valid weights pairs) : weight weights pairs ≤ assignmentWeight weights (extend hv) := by
  classical
  let rows : Finset (L ⊕ R) := pairs.image (fun p => Sum.inl p.1)
  calc
    weight weights pairs ≤ ∑ p ∈ pairs, profit weights (.inl p.1) (extend hv (.inl p.1)) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [extend_pair hv hp]
      exact le_max_right _ _
    _ = ∑ x ∈ rows, profit weights x (extend hv x) := by
      symm
      apply Finset.sum_image
      intro p hp q hq he
      exact hv.2.1 p hp q hq (Sum.inl.inj he)
    _ ≤ assignmentWeight weights (extend hv) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ rows)
      intro x _ _
      cases x with
      | inl l => cases extend hv (.inl l) <;> simp [profit]
      | inr r => simp [profit]

/-- A maximum complete assignment decodes to an optimal partial matching.
This theorem is independent of which assignment algorithm supplies optimality. -/
theorem maximum_assignment_decodes {weights : L → R → Option ℝ}
    (σ : Equiv.Perm (L ⊕ R))
    (hmax : ∀ τ, assignmentWeight weights τ ≤ assignmentWeight weights σ) :
    IsMaximum weights (decode weights σ) := by
  refine ⟨decode_valid weights σ, ?_⟩
  intro pairs hv
  rw [decode_weight]
  exact (weight_le_extend hv).trans (hmax (extend hv))

/-- Subtracting each profit from one common constant converts maximization
into complete minimum-cost assignment. -/
def assignmentCost (weights : L → R → Option ℝ) (shift : ℝ)
    (σ : Equiv.Perm (L ⊕ R)) : ℝ :=
  ∑ x, (shift - profit weights x (σ x))

theorem assignmentCost_eq (weights : L → R → Option ℝ) (shift : ℝ)
    (σ : Equiv.Perm (L ⊕ R)) :
    assignmentCost weights shift σ =
      (Fintype.card L + Fintype.card R : ℕ) * shift - assignmentWeight weights σ := by
  simp [assignmentCost, assignmentWeight, Finset.sum_sub_distrib, Fintype.card_sum]

/-- Complete minimum-cost assignment suffices for the optional, forbidden,
signed maximum-weight matching problem. The shift may be any real number. -/
theorem minimum_assignment_decodes {weights : L → R → Option ℝ}
    (shift : ℝ) (σ : Equiv.Perm (L ⊕ R))
    (hmin : ∀ τ, assignmentCost weights shift σ ≤ assignmentCost weights shift τ) :
    IsMaximum weights (decode weights σ) := by
  apply maximum_assignment_decodes σ
  intro τ
  have h := hmin τ
  rw [assignmentCost_eq, assignmentCost_eq] at h
  exact (sub_le_sub_iff_left _).mp h

end SubtreeProofs.WeightedMatching.AssignmentReduction

end
