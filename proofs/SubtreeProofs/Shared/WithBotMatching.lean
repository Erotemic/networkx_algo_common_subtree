module

public import SubtreeProofs.Shared.WeightedMatching
public import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Tactic

/-!
# Removing negative-infinity edges before finite-weight assignment

Graph recurrences use `WithBot K` scores. An allowed edge of weight bottom
cannot improve an optional matching over the empty matching. It can therefore
be forbidden before invoking a finite integer or real assignment solver.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching

variable {L R K : Type*} [DecidableEq L] [DecidableEq R]
  [AddCommMonoid K] [LinearOrder K]

/-- Both incompatible and bottom-weight pairs are forbidden in finite arithmetic. -/
def finiteWeights (weights : L → R → Option (WithBot K)) (l : L) (r : R) : Option K :=
  match weights l r with
  | none => none
  | some value => value

omit [DecidableEq L] [DecidableEq R] [AddCommMonoid K] [LinearOrder K] in
@[simp] theorem finiteWeights_eq_some_iff (weights : L → R → Option (WithBot K)) (l : L) (r : R) (k : K) :
    finiteWeights weights l r = some k ↔ weights l r = some (k : WithBot K) := by
  cases h : weights l r with
  | none => simp [finiteWeights, h]
  | some value =>
    simp only [finiteWeights, h]
    change (value = (k : WithBot K)) ↔ some value = some (k : WithBot K)
    simp

omit [DecidableEq L] [DecidableEq R] [AddCommMonoid K] [LinearOrder K] in
theorem finiteWeights_ne_none_iff (weights : L → R → Option (WithBot K)) (l : L) (r : R) :
    finiteWeights weights l r ≠ none ↔ weights l r ≠ none ∧ weights l r ≠ some ⊥ := by
  cases h : weights l r with
  | none => simp [finiteWeights, h]
  | some value =>
    simp only [finiteWeights, h]
    change value ≠ (⊥ : WithBot K) ↔ some value ≠ none ∧ some value ≠ some (⊥ : WithBot K)
    simp

omit [DecidableEq L] [DecidableEq R] [AddCommMonoid K] [LinearOrder K] in
theorem valid_of_finiteWeights {weights : L → R → Option (WithBot K)} {pairs : Finset (L × R)}
    (h : Valid (finiteWeights weights) pairs) : Valid weights pairs :=
  ⟨fun p hp => ((finiteWeights_ne_none_iff weights p.1 p.2).mp (h.1 p hp)).1, h.2⟩

omit [DecidableEq L] [DecidableEq R] [LinearOrder K] in
theorem weight_of_finiteWeights {weights : L → R → Option (WithBot K)} {pairs : Finset (L × R)}
    (h : Valid (finiteWeights weights) pairs) :
    weight weights pairs = (weight (finiteWeights weights) pairs : K) := by
  unfold weight
  rw [WithBot.coe_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp (h.1 p hp)
  have hw := (finiteWeights_eq_some_iff weights p.1 p.2 k).mp hk
  simp [hk, hw]

omit [DecidableEq L] [DecidableEq R] in
/-- A finite-weight maximum is also a maximum for the original bottom-valued
objective. A competitor using any bottom edge has bottom total weight. -/
theorem maximum_of_finiteWeights {weights : L → R → Option (WithBot K)} {pairs : Finset (L × R)}
    (h : IsMaximum (finiteWeights weights) pairs) : IsMaximum weights pairs := by
  refine ⟨valid_of_finiteWeights h.1, ?_⟩
  intro other hv
  by_cases hb : ∃ p ∈ other, weights p.1 p.2 = some ⊥
  · obtain ⟨p, hp, hw⟩ := hb
    have hs : weight weights other = ⊥ := by
      apply WithBot.sum_eq_bot_iff.mpr
      exact ⟨p, hp, by simp [hw]⟩
    rw [hs]
    exact bot_le
  · have hfinite : Valid (finiteWeights weights) other := by
      refine ⟨?_, hv.2⟩
      intro p hp
      exact (finiteWeights_ne_none_iff weights p.1 p.2).mpr
        ⟨hv.1 p hp, fun hw => hb ⟨p, hp, hw⟩⟩
    rw [weight_of_finiteWeights hfinite, weight_of_finiteWeights h.1]
    exact_mod_cast h.2 other hfinite

end SubtreeProofs.WeightedMatching

end
