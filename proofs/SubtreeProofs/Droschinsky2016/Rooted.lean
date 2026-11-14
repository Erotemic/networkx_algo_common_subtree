module

public import SubtreeProofs.Droschinsky2016.Witness
public import SubtreeProofs.Shared.RootedTree

/-!
# Rooted subproblems and the fixed-root reduction

Rooted witnesses are restrictions of the independent connected-isomorphism
problem to descendant subtrees, with the two subproblem roots mapped together.
The score continues to be the independent vertex/edge sum. The fixed-root
identity is Lemma 2's variational equality; no recurrence is used to define it.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Root-to-root witnesses within the two specified descendant subtrees. -/
def RootedValid (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) (pairs : Mapping V W) : Prop :=
  Valid left right pairs ∧ (u,v) ∈ pairs ∧
    ∀ p ∈ pairs, left.Ancestor leftBase u p.1 ∧ right.Ancestor rightBase v p.2

omit [Fintype V] [Fintype W] in
theorem rooted_singleton_valid (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) :
    RootedValid left right leftBase rightBase u v {(u,v)} := by
  refine ⟨singleton_valid left right u v, by simp, ?_⟩
  intro p hp
  obtain rfl := Finset.mem_singleton.mp hp
  exact ⟨left.ancestor_refl _ _, right.ancestor_refl _ _⟩

omit [Fintype V] [Fintype W] in
/-- Every independent witness has a unique mapped vertex nearest a fixed
left root, and all selected vertices lie in its descendant subtree. -/
theorem Valid.fixed_root_representative {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root : V) :
    ∃! p, p ∈ pairs ∧ RootedValid left right root p.2 p.1 p.2 pairs := by
  have hn : (pairs.image Prod.fst).Nonempty := h.1.image Prod.fst
  obtain ⟨u, ⟨hu, htop⟩, huniq⟩ :=
    left.connected_exists_unique_top (pairs.image Prod.fst) hn h.2.2.1 root
  obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
  refine ⟨p, ⟨hp, h, hp, ?_⟩, ?_⟩
  · intro q hq
    refine ⟨?_, right.root_ancestor _ _⟩
    rw [hpu]
    exact htop q.1 (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  · intro q hq
    apply h.2.1.1 q hq.1 p hp
    rw [hpu]
    apply huniq q.1
    refine ⟨Finset.mem_image.mpr ⟨q, hq.1, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨entry, he, rfl⟩ := Finset.mem_image.mp hx
    exact (hq.2.2.2 entry he).1

/-- The finite rooted feasible family, specified without a DP. -/
noncomputable def rootedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) : Finset (Mapping V W) := by
  classical
  exact (Finset.univ.powerset).filter (RootedValid left right leftBase rightBase u v)

@[simp] theorem mem_rootedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) (pairs : Mapping V W) :
    pairs ∈ rootedFeasible left right leftBase rightBase u v ↔
      RootedValid left right leftBase rightBase u v pairs := by
  classical
  simp [rootedFeasible]

/-- Exact independent rooted optimum, retaining negative and bottom scores. -/
noncomputable def rootedValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase : V) (rightBase : W) (u : V) (v : W) : WithBot K :=
  (rootedFeasible left right leftBase rightBase u v).sup (score left weights)

omit [IsStrictOrderedRing K] in
theorem rooted_score_le_value {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W K) {leftBase u : V} {rightBase v : W} {pairs : Mapping V W}
    (h : RootedValid left right leftBase rightBase u v pairs) :
    score left weights pairs ≤ rootedValue left right weights leftBase rightBase u v :=
  Finset.le_sup (f := score left weights) ((mem_rootedFeasible _ _ _ _ _ _ _).mpr h)

omit [IsStrictOrderedRing K] in
/-- Every rooted optimum has a concrete independently valid witness. -/
theorem rootedValue_attained (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (leftBase u : V) (rightBase v : W) :
    ∃ pairs, RootedValid left right leftBase rightBase u v pairs ∧
      score left weights pairs = rootedValue left right weights leftBase rightBase u v := by
  have hn : (rootedFeasible left right leftBase rightBase u v).Nonempty :=
    ⟨{(u,v)}, (mem_rootedFeasible _ _ _ _ _ _ _).mpr (rooted_singleton_valid _ _ _ _ _ _)⟩
  obtain ⟨pairs, hp, hmax⟩ := Finset.exists_max_image
    (rootedFeasible left right leftBase rightBase u v) (score left weights) hn
  refine ⟨pairs, (mem_rootedFeasible _ _ _ _ _ _ _).mp hp, ?_⟩
  exact le_antisymm (Finset.le_sup (f := score left weights) hp) (Finset.sup_le hmax)

/-- Exact independent unrestricted optimum. -/
noncomputable def unrootedValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) : WithBot K :=
  (feasible left right).sup (score left weights)

/-- The source's restricted family: one fixed left orientation, all descendant
roots on the left, and the whole right tree rooted at every possible vertex. -/
noncomputable def fixedRootValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V) : WithBot K :=
  Finset.univ.sup (fun u => Finset.univ.sup (fun v => rootedValue left right weights root v u v))

omit [IsStrictOrderedRing K] in
/-- 2016 Lemma 2: fixing one tree's root does not change the optimum. -/
theorem fixedRootValue_eq_unrootedValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W K) (root : V) :
    fixedRootValue left right weights root = unrootedValue left right weights := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v _
    apply Finset.sup_le
    intro pairs hp
    have hv := ((mem_rootedFeasible left right root v u v pairs).mp hp).1
    exact Finset.le_sup (f := score left weights) ((mem_feasible left right pairs).mpr hv)
  · apply Finset.sup_le
    intro pairs hp
    have hv := (mem_feasible left right pairs).mp hp
    obtain ⟨p, ⟨_, hrooted⟩, _⟩ := hv.fixed_root_representative root
    have hlocal : score left weights pairs ≤ rootedValue left right weights root p.2 p.1 p.2 :=
      Finset.le_sup (f := score left weights)
        ((mem_rootedFeasible left right root p.2 p.1 p.2 pairs).mpr hrooted)
    exact hlocal.trans ((Finset.le_sup (f := fun v => rootedValue left right weights root v p.1 v)
      (Finset.mem_univ p.2)).trans (Finset.le_sup
        (f := fun u => Finset.univ.sup (fun v => rootedValue left right weights root v u v))
        (Finset.mem_univ p.1)))

end SubtreeProofs.Droschinsky2016

end
