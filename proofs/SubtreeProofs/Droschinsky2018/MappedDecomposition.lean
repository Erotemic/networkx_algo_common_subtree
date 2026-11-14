module

public import SubtreeProofs.Droschinsky2018.ScoreDecomposition
public import SubtreeProofs.Droschinsky2018.MatchingAssembly

/-!
# Decomposing every mapped-root witness into a compatible child matching

The first target edges of distinct common-child paths give distinct matching
endpoints. Restricting each actual common-child region produces an independently
valid boundary witness, and its exact score is bounded by the matching entry.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018.MappedDecomposition

open Droschinsky2016

variable {A V W : Type*} [Fintype A] [DecidableEq A] [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {common : FiniteTree A} {left : FiniteTree V} {right : FiniteTree W}
  {root : A} {leftBase : V} {rightBase : W}
  (first : RootedTopologicalEmbedding common left root leftBase)
  (second : RootedTopologicalEmbedding common right root rightBase)

attribute [local instance] Classical.propDecidable

noncomputable def branchPairs (c : RootedDecomposition.Index common root) : Mapping V W :=
  pairedImage (ScoreDecomposition.branch common root first.toUnrooted c)
    (ScoreDecomposition.branch common root second.toUnrooted c)

omit [Fintype V] [Fintype W] in
/-- Restricting an arbitrary common-child region gives a feasible continuation
at the corresponding immediate input-child pair. -/
theorem branch_state_valid (c : RootedDecomposition.Index common root) :
    StateValid left right leftBase rightBase (first.branchChild c) (second.branchChild c)
      (branchPairs first second c) (first.map c.val, second.map c.val) := by
  refine ⟨pairedImage_valid _ _, (mem_pairedImage _ _ _ _).mpr
    ⟨RootedDecomposition.branchRoots common root c, rfl, rfl⟩, ?_, first.branchChild_top c, second.branchChild_top c⟩
  intro p hp
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨first.ancestor_preserved a.property, second.ancestor_preserved a.property⟩

noncomputable def childMatching : Mapping V W :=
  Finset.univ.image (fun c : RootedDecomposition.Index common root => (first.branchChild c, second.branchChild c))

/-- The concrete first-child pairs form an allowed partial matching. -/
theorem childMatching_valid (weights : Scoring V W) (penalty : WithTop ℝ) :
    WeightedMatching.Valid (stateChildWeights left right weights penalty leftBase rightBase (first.map root) (second.map root))
      (childMatching first second) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    exact (stateChildWeights_allowed _ _ _ _ _ _ _ _ _ _).mpr ⟨first.branchChild_valid c, second.branchChild_valid c⟩
  · intro p hp q hq he
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg (fun c => (first.branchChild c, second.branchChild c)) (first.branchChild_injective he)
  · intro p hp q hq he
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg (fun c => (first.branchChild c, second.branchChild c)) (second.branchChild_injective he)

/-- Each source common-child branch is counted once in the child matching. -/
theorem childMatching_weight (weights : Scoring V W) (penalty : WithTop ℝ) :
    WeightedMatching.weight (stateChildWeights left right weights penalty leftBase rightBase (first.map root) (second.map root))
      (childMatching first second) = ∑ c : RootedDecomposition.Index common root,
        matchingBranchValue left right weights penalty leftBase rightBase (first.map root) (second.map root)
          (first.branchChild c) (second.branchChild c) := by
  unfold WeightedMatching.weight
  rw [childMatching, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro c _
    exact stateChildWeights_get _ _ _ _ _ _ _ _ _ _ ⟨first.branchChild_valid c, second.branchChild_valid c⟩
  · intro c _ d _ he
    exact first.branchChild_injective (congrArg Prod.fst he)

/-- Every independent source-style mapped-root witness is bounded by the
certified child matching optimum. -/
theorem source_score_upper (weights : Scoring V W) (penalty : WithTop ℝ) :
    realizationScore first.toUnrooted second.toUnrooted weights penalty ≤ weights.node (first.map root) (second.map root) +
      WeightedMatching.weight
        (stateChildWeights left right weights penalty leftBase rightBase (first.map root) (second.map root))
        (bestStateMatching left right weights penalty leftBase rightBase (first.map root) (second.map root)) := by
  have hscore := ScoreDecomposition.score_decomposition common root first.toUnrooted second.toUnrooted weights penalty
  rw [hscore]
  apply (add_le_add le_rfl ?_).trans
    (add_le_add le_rfl ((bestStateMatching_correct left right weights penalty leftBase rightBase (first.map root) (second.map root)).2
      (childMatching first second) (childMatching_valid first second weights penalty)))
  rw [childMatching_weight first second weights penalty]
  apply Finset.sum_le_sum
  intro c _
  have hbranch := branch_state_valid first second c
  have hle := connecting_reward_le_branchValue weights penalty (first.branchChild_valid c) (second.branchChild_valid c)
    (w := (branchPairs first second c, (first.map c.val, second.map c.val))) hbranch
  have he := score_pairedImage (ScoreDecomposition.branch common root first.toUnrooted c)
    (ScoreDecomposition.branch common root second.toUnrooted c) weights penalty
  change pathScore left right weights penalty s(first.map root, first.map c.val) s(second.map root, second.map c.val) +
    realizationScore (ScoreDecomposition.branch common root first.toUnrooted c)
      (ScoreDecomposition.branch common root second.toUnrooted c) weights penalty ≤ _
  exact (add_le_add le_rfl he.symm.le).trans hle

end SubtreeProofs.Droschinsky2018.MappedDecomposition

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Reverse mapped-state inequality from decomposition of every independent
feasible mapped-root witness. -/
theorem mappedValue_le_matchingValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    mappedValue left right weights penalty leftBase rightBase u v ≤ weights.node u v +
      WeightedMatching.weight (stateChildWeights left right weights penalty leftBase rightBase u v)
        (bestStateMatching left right weights penalty leftBase rightBase u v) := by
  apply Finset.sup_le
  intro w hw
  obtain ⟨hv, he⟩ := (mem_mappedFeasible left right leftBase rightBase u v w).mp hw
  let pointed := hv.pointed
  have hs := MappedDecomposition.source_score_upper pointed.first pointed.second weights penalty
  rw [pointed.score_eq, pointed.root_left, pointed.root_right, he] at hs
  rw [he, stateScore_mapped]
  exact hs

/-- 2018 Lemma 5's mapped-root matching recurrence, against the independent
boundary-state optimum and with an actual certified partial-matching oracle. -/
theorem mapped_recurrence (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    mappedValue left right weights penalty leftBase rightBase u v = weights.node u v +
      WeightedMatching.weight (stateChildWeights left right weights penalty leftBase rightBase u v)
        (bestStateMatching left right weights penalty leftBase rightBase u v) :=
  le_antisymm (mappedValue_le_matchingValue left right weights penalty leftBase rightBase u v)
    (matchingValue_le_mappedValue left right weights penalty leftBase rightBase u v)

end SubtreeProofs.Droschinsky2018

end
