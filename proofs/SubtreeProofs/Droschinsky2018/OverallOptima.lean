module

public import SubtreeProofs.Droschinsky2018.MappedDecomposition

/-!
# Recovering the overall rooted and unrooted objectives from mapped states

The independent source objectives are nonempty finite witness maxima. The
rooted problem takes the largest mapped entry in its fixed orientations;
trying every pair of ambient roots gives a correct unrooted baseline.
Neither identity claims the optimized unrooted paper algorithm.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem rooted_score_le_value {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {leftRoot : V} {rightRoot : W} {pairs : Mapping V W}
    (h : RootedValid left right leftRoot rightRoot pairs) :
    score left right weights penalty pairs ≤ rootedValue left right weights penalty leftRoot rightRoot :=
  Finset.le_sup (s := rootedFeasible left right leftRoot rightRoot) (f := score left right weights penalty)
    ((mem_rootedFeasible _ _ _ _ _).mpr h)

/-- The rooted source optimum is exactly the maximum mapped-state value in
its supplied input orientations. Boundary skips above the common root are free. -/
theorem rootedValue_eq_max_mapped (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftRoot : V) (rightRoot : W) :
    rootedValue left right weights penalty leftRoot rightRoot =
      Finset.univ.sup (fun u => Finset.univ.sup (fun v => mappedValue left right weights penalty leftRoot rightRoot u v)) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro pairs hp
    obtain ⟨hv, top, ht, htop⟩ := (mem_rootedFeasible left right leftRoot rightRoot pairs).mp hp
    have hs : StateValid left right leftRoot rightRoot top.1 top.2 pairs top :=
      ⟨hv, ht, htop, left.ancestor_refl _ _, right.ancestor_refl _ _⟩
    have hle := stateScore_le_mappedValue weights penalty hs (by cases top; rfl)
    have heq : stateScore left right weights penalty top.1 top.2 pairs top = score left right weights penalty pairs :=
      stateScore_mapped left right weights penalty top.1 top.2 pairs
    rw [heq] at hle
    exact hle.trans ((Finset.le_sup (s := Finset.univ)
      (f := fun v => mappedValue left right weights penalty leftRoot rightRoot top.1 v) (Finset.mem_univ top.2)).trans
        (Finset.le_sup (s := Finset.univ)
          (f := fun u => Finset.univ.sup (fun v => mappedValue left right weights penalty leftRoot rightRoot u v))
          (Finset.mem_univ top.1)))
  · apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v _
    apply Finset.sup_le
    intro w hw
    obtain ⟨hv, he⟩ := (mem_mappedFeasible left right leftRoot rightRoot u v w).mp hw
    rw [he, stateScore_mapped]
    exact rooted_score_le_value weights penalty hv.toRootedValid

/-- Independent unrestricted unrooted optimum, with no zero clamp. -/
noncomputable def unrootedValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) : WithBot ℝ :=
  (feasible left right).sup (score left right weights penalty)

theorem unrooted_score_le_value {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {pairs : Mapping V W} (h : Valid left right pairs) :
    score left right weights penalty pairs ≤ unrootedValue left right weights penalty :=
  Finset.le_sup (s := feasible left right) (f := score left right weights penalty) ((mem_feasible _ _ _).mpr h)

/-- Trying every root pair and keeping only its root-to-root mapped optimum
solves the unrooted objective. This is the straightforward rerooting baseline. -/
theorem unrootedValue_eq_max_rerooted_mapped (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) :
    unrootedValue left right weights penalty =
      Finset.univ.sup (fun u => Finset.univ.sup (fun v => mappedValue left right weights penalty u v u v)) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro pairs hp
    have hv := (mem_feasible left right pairs).mp hp
    obtain ⟨top, ht⟩ := hv.1
    have hs : StateValid left right top.1 top.2 top.1 top.2 pairs top :=
      ⟨hv, ht, fun p _ => ⟨left.root_ancestor _ _, right.root_ancestor _ _⟩,
        left.ancestor_refl _ _, right.ancestor_refl _ _⟩
    have hle := stateScore_le_mappedValue weights penalty hs (by cases top; rfl)
    have heq : stateScore left right weights penalty top.1 top.2 pairs top = score left right weights penalty pairs :=
      stateScore_mapped left right weights penalty top.1 top.2 pairs
    rw [heq] at hle
    exact hle.trans ((Finset.le_sup (s := Finset.univ)
      (f := fun v => mappedValue left right weights penalty top.1 v top.1 v) (Finset.mem_univ top.2)).trans
        (Finset.le_sup (s := Finset.univ)
          (f := fun u => Finset.univ.sup (fun v => mappedValue left right weights penalty u v u v))
          (Finset.mem_univ top.1)))
  · apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v _
    apply Finset.sup_le
    intro w hw
    obtain ⟨hv, he⟩ := (mem_mappedFeasible left right u v u v w).mp hw
    rw [he, stateScore_mapped]
    exact unrooted_score_le_value weights penalty hv.1

end SubtreeProofs.Droschinsky2018

end
