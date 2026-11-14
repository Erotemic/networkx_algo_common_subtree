module

public import SubtreeProofs.Droschinsky2018.SkippedRecurrence
public import SubtreeProofs.Droschinsky2018.BranchReward

/-!
# Exact matching-branch values and attaining continuation witnesses

The candidate weight in Lemma 5 is bounded above by the two independent state
optima, and is attained by an actual boundary witness. Empty skipped families
are handled without inventing a witness for their negative-infinity value.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

open Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

noncomputable def matchingBranchValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (penalty : WithTop K) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (c : V) (d : W) : WithBot K :=
  max (weights.edge s(u,c) s(v,d) + mappedValue left right weights penalty leftBase rightBase c d)
    (skippedValue left right weights penalty leftBase rightBase c d)

/-- Every independently valid branch witness has reward at most the candidate
matching weight derived from the two independent state optima. -/
theorem connecting_reward_le_branchValue {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W K) (penalty : WithTop K) {leftBase u c : V} {rightBase v d : W}
    (hc : left.Child leftBase u c) (hd : right.Child rightBase v d) {w : BoundaryWitness V W}
    (h : StateValid left right leftBase rightBase c d w.1 w.2) :
    pathScore left right weights penalty s(u,w.2.1) s(v,w.2.2) + score left right weights penalty w.1 ≤
      matchingBranchValue left right weights penalty leftBase rightBase u v c d := by
  rw [connecting_reward_boundary weights penalty w.1 w.2 hc hd h.2.2.2.1 h.2.2.2.2]
  split
  · rename_i he
    exact (add_le_add le_rfl (stateScore_le_mappedValue weights penalty h he)).trans (le_max_left _ _)
  · rename_i he
    exact (stateScore_le_skippedValue weights penalty h he).trans (le_max_right _ _)

/-- The candidate matching weight is attained by an actual continuation.
Mapped witnesses always exist; skipped witnesses are selected only when their
value strictly improves over a mapped candidate and hence is not bottom. -/
theorem matchingBranchValue_attained {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W K) (penalty : WithTop K) {leftBase u c : V} {rightBase v d : W}
    (hc : left.Child leftBase u c) (hd : right.Child rightBase v d) :
    ∃ w : BoundaryWitness V W, StateValid left right leftBase rightBase c d w.1 w.2 ∧
      pathScore left right weights penalty s(u,w.2.1) s(v,w.2.2) + score left right weights penalty w.1 =
        matchingBranchValue left right weights penalty leftBase rightBase u v c d := by
  by_cases hcmp : skippedValue left right weights penalty leftBase rightBase c d ≤
      weights.edge s(u,c) s(v,d) + mappedValue left right weights penalty leftBase rightBase c d
  · obtain ⟨w, hv, he, hs⟩ := mappedValue_attained left right weights penalty leftBase c rightBase d
    refine ⟨w, hv, ?_⟩
    rw [connecting_reward_boundary weights penalty w.1 w.2 hc hd hv.2.2.2.1 hv.2.2.2.2,
      ite_eq_left he, hs]
    exact (max_eq_left hcmp).symm
  · have hn : skippedValue left right weights penalty leftBase rightBase c d ≠ ⊥ := by
      intro he
      apply hcmp
      rw [he]
      exact bot_le
    obtain ⟨w, hv, he, hs⟩ := skippedValue_attained_of_ne_bot left right weights penalty leftBase c rightBase d hn
    refine ⟨w, hv, ?_⟩
    rw [connecting_reward_boundary weights penalty w.1 w.2 hc hd hv.2.2.2.1 hv.2.2.2.2,
      ite_eq_right he, hs]
    exact (max_eq_right (le_of_lt (lt_of_not_ge hcmp))).symm

end SubtreeProofs.Droschinsky2018

end
