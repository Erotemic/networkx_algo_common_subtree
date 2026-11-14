module

public import SubtreeProofs.Droschinsky2016.Specification

/-!
# Independent topological skeletons and distance-penalized scores

Selected vertices induce a skeleton only when the unique paths form a tree
with disjoint interiors. Omitting a branch point is not silently permitted.
This file specifies the unrooted problem; rooted ancestry restrictions are a
separate refinement. Direct-edge rewards follow Definition 4 exactly.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

open Droschinsky2016

/-- Two selected vertices are consecutive when no selected vertex is internal
to their unique path. -/
def BranchAdjacent (tree : FiniteTree V) (selected : Finset V) (first second : V) : Prop :=
  first ≠ second ∧ Disjoint (tree.pathInterior first second) selected

omit [Fintype V] in
theorem branchAdjacent_comm (tree : FiniteTree V) (selected : Finset V) (first second : V) :
    BranchAdjacent tree selected first second ↔ BranchAdjacent tree selected second first := by
  unfold BranchAdjacent
  rw [tree.pathInterior_comm]
  exact and_congr ne_comm Iff.rfl

/-- The candidate skeleton graph, before its tree invariant is imposed. -/
noncomputable def skeleton (tree : FiniteTree V) (selected : Finset V) :
    SimpleGraph (↑(selected : Set V)) where
  Adj first second := BranchAdjacent tree selected first.val second.val
  symm := ⟨fun first second h => (branchAdjacent_comm tree selected first.val second.val).mp h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype V] in
/-- A selected singleton is a genuine one-vertex skeleton. -/
theorem skeleton_singleton_isTree (tree : FiniteTree V) (vertex : V) :
    (skeleton tree {vertex}).IsTree := by
  let : Nonempty (↑(↑({vertex} : Finset V) : Set V)) := ⟨⟨vertex, by simp⟩⟩
  let : Subsingleton (↑(↑({vertex} : Finset V) : Set V)) := ⟨by
    rintro ⟨first, hf⟩ ⟨second, hs⟩
    apply Subtype.ext
    simp only [Finset.mem_coe, Finset.mem_singleton] at hf hs
    exact hf.trans hs.symm⟩
  exact SimpleGraph.IsTree.of_subsingleton

/-- Consecutive selected endpoints as an unordered pair. -/
noncomputable def branchAdj (tree : FiniteTree V) (selected : Finset V) : Sym2 V → Prop :=
  Sym2.lift ⟨BranchAdjacent tree selected,
    fun first second => propext (branchAdjacent_comm tree selected first second)⟩

noncomputable def skeletonEdges (tree : FiniteTree V) (selected : Finset V) : Finset (Sym2 V) := by
  classical
  exact selected.sym2.filter (branchAdj tree selected)

/-- Unique-path lengths are independent of the orientation of an abstract edge. -/
noncomputable def pathLength (tree : FiniteTree V) : Sym2 V → Nat :=
  Sym2.lift ⟨tree.pathLength, tree.pathLength_comm⟩

noncomputable def pathInterior (tree : FiniteTree V) : Sym2 V → Finset V :=
  Sym2.lift ⟨tree.pathInterior, tree.pathInterior_comm⟩

/-- Distinct skeleton edges must not share an interior vertex. -/
def InteriorDisjoint (tree : FiniteTree V) (selected : Finset V) : Prop :=
  ∀ first ∈ skeletonEdges tree selected, ∀ second ∈ skeletonEdges tree selected,
    first ≠ second → Disjoint (pathInterior tree first) (pathInterior tree second)

/-- A concrete nonempty unrooted topological common-tree witness. -/
def Valid (left : FiniteTree V) (right : FiniteTree W) (pairs : Mapping V W) : Prop :=
  pairs.Nonempty ∧ PartialBijection pairs ∧
    (skeleton left (pairs.image Prod.fst)).IsTree ∧
    (skeleton right (pairs.image Prod.snd)).IsTree ∧
    InteriorDisjoint left (pairs.image Prod.fst) ∧ InteriorDisjoint right (pairs.image Prod.snd) ∧
    ∀ p ∈ pairs, ∀ q ∈ pairs,
      BranchAdjacent left (pairs.image Prod.fst) p.1 q.1 ↔
        BranchAdjacent right (pairs.image Prod.snd) p.2 q.2

/-- Finite penalties and the infinite penalty are represented explicitly.
Source problems require `0 ≤ penalty`; the score is defined for every value. -/
noncomputable def skippedScore (penalty : WithTop ℝ) (skipped : Nat) : WithBot ℝ :=
  if penalty = ⊤ then if skipped = 0 then 0 else ⊥
  else ((-(penalty.untopD 0) * (skipped : ℝ)) : ℝ)

/-- Definition 4: both paths must be single edges for an edge-label reward. -/
noncomputable def pathScore (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (first : Sym2 V) (second : Sym2 W) : WithBot ℝ :=
  if pathLength left first = 1 ∧ pathLength right second = 1 then weights.edge first second
  else skippedScore penalty ((pathLength left first - 1) + (pathLength right second - 1))

/-- Abstract common edges as unordered pairs of mapped vertices. -/
noncomputable def mappedEdges (left : FiniteTree V) (pairs : Mapping V W) : Finset (Sym2 (V × W)) := by
  classical
  exact pairs.sym2.filter (fun edge => branchAdj left (pairs.image Prod.fst) (edge.map Prod.fst))

/-- Score each selected vertex and each abstract topological path pair once. -/
noncomputable def score (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (pairs : Mapping V W) : WithBot ℝ :=
  (∑ pair ∈ pairs, weights.node pair.1 pair.2) +
    ∑ edge ∈ mappedEdges left pairs, pathScore left right weights penalty (edge.map Prod.fst) (edge.map Prod.snd)

def IsMaximum (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (pairs : Mapping V W) : Prop :=
  Valid left right pairs ∧ ∀ other, Valid left right other →
    score left right weights penalty other ≤ score left right weights penalty pairs

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Labels contribute on direct paths exactly as printed. -/
theorem pathScore_direct (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (first : Sym2 V) (second : Sym2 W)
    (hl : pathLength left first = 1) (hr : pathLength right second = 1) :
    pathScore left right weights penalty first second = weights.edge first second := by
  simp [pathScore, hl, hr]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- On longer paths, changing any edge reward cannot affect the contribution. -/
theorem pathScore_skipped (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (first : Sym2 V) (second : Sym2 W)
    (h : ¬ (pathLength left first = 1 ∧ pathLength right second = 1)) :
    pathScore left right weights penalty first second =
      skippedScore penalty ((pathLength left first - 1) + (pathLength right second - 1)) := by
  simp only [pathScore, h, ↓reduceIte]


omit [Fintype V] in
@[simp] theorem skeletonEdges_singleton (tree : FiniteTree V) (vertex : V) :
    skeletonEdges tree {vertex} = ∅ := by
  classical
  rw [skeletonEdges, Finset.sym2_singleton]
  apply Finset.filter_eq_empty_iff.mpr
  intro edge he
  have heq := Finset.mem_singleton.mp he
  subst edge
  change ¬ BranchAdjacent tree {vertex} vertex vertex
  simp [BranchAdjacent]

omit [Fintype V] [Fintype W] in
/-- A singleton is feasible regardless of labels, signs or the penalty value. -/
theorem singleton_valid (left : FiniteTree V) (right : FiniteTree W) (u : V) (v : W) :
    Valid left right {(u,v)} := by
  have hleft : ({(u,v)} : Mapping V W).image Prod.fst = {u} := Finset.image_singleton _ _
  have hright : ({(u,v)} : Mapping V W).image Prod.snd = {v} := Finset.image_singleton _ _
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PartialBijection]
  · rw [hleft]
    exact skeleton_singleton_isTree left u
  · rw [hright]
    exact skeleton_singleton_isTree right v
  · simp [hleft, InteriorDisjoint]
  · simp [hright, InteriorDisjoint]
  · intro first hf second hs
    have hf' := Finset.mem_singleton.mp hf
    have hs' := Finset.mem_singleton.mp hs
    subst first
    subst second
    simp [BranchAdjacent]

omit [Fintype V] [Fintype W] [DecidableEq W] in
@[simp] theorem mappedEdges_singleton (left : FiniteTree V) (u : V) (v : W) :
    mappedEdges left {(u,v)} = ∅ := by
  classical
  rw [mappedEdges, Finset.sym2_singleton]
  apply Finset.filter_eq_empty_iff.mpr
  intro edge he
  have heq := Finset.mem_singleton.mp he
  subst edge
  change ¬ BranchAdjacent left (({(u,v)} : Mapping V W).image Prod.fst) u u
  simp [BranchAdjacent]

omit [Fintype V] [Fintype W] [DecidableEq W] in
@[simp] theorem score_singleton (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (u : V) (v : W) :
    score left right weights penalty {(u,v)} = weights.node u v := by
  simp [score]


omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- The 1-edge/2-edge discriminator contributes only one skipped-vertex penalty,
even if the edge reward is incompatible or arbitrarily large. -/
theorem one_two_path_score (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : ℝ) (first : Sym2 V) (second : Sym2 W)
    (hl : pathLength left first = 1) (hr : pathLength right second = 2) :
    pathScore left right weights penalty first second = ((-penalty : ℝ) : WithBot ℝ) := by
  simp [pathScore, hl, hr, skippedScore]

/-- Increasing a finite penalty decreases every skipped-path contribution. -/
theorem skippedScore_antitone (first second : ℝ) (h : first ≤ second) (skipped : Nat) :
    skippedScore (second : WithTop ℝ) skipped ≤ skippedScore (first : WithTop ℝ) skipped := by
  simp only [skippedScore, WithTop.coe_ne_top, ↓reduceIte, WithTop.untopD_coe]
  exact_mod_cast mul_le_mul_of_nonneg_right (neg_le_neg h) (Nat.cast_nonneg skipped)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Penalty monotonicity holds per abstract path, without any edge-reward assumption. -/
theorem pathScore_antitone (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (first second : ℝ) (h : first ≤ second) (leftEdge : Sym2 V) (rightEdge : Sym2 W) :
    pathScore left right weights second leftEdge rightEdge ≤
      pathScore left right weights first leftEdge rightEdge := by
  unfold pathScore
  split
  · exact le_refl _
  · exact skippedScore_antitone first second h _

omit [Fintype V] [Fintype W] [DecidableEq W] in
/-- Penalty monotonicity of every independently specified witness score. -/
theorem score_antitone (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (first second : ℝ) (h : first ≤ second) (pairs : Mapping V W) :
    score left right weights second pairs ≤ score left right weights first pairs := by
  unfold score
  exact add_le_add (le_refl _)
    (Finset.sum_le_sum (fun edge _ => pathScore_antitone left right weights first second h _ _))

/-- The feasible family is finite independently of any branch recurrence. -/
noncomputable def feasible (left : FiniteTree V) (right : FiniteTree W) : Finset (Mapping V W) := by
  classical
  exact (Finset.univ.powerset).filter (Valid left right)

@[simp] theorem mem_feasible (left : FiniteTree V) (right : FiniteTree W) (pairs : Mapping V W) :
    pairs ∈ feasible left right ↔ Valid left right pairs := by
  classical
  simp [feasible]

/-- The finite nonempty witness family has an attained optimum. -/
theorem exists_maximum_of_feasible (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (h : ∃ pairs, Valid left right pairs) :
    ∃ pairs, IsMaximum left right weights penalty pairs := by
  classical
  obtain ⟨pairs, hpairs⟩ := h
  have hf : (feasible left right).Nonempty := ⟨pairs, (mem_feasible _ _ _).mpr hpairs⟩
  obtain ⟨best, hbest, hmaximum⟩ := Finset.exists_max_image (feasible left right) (score left right weights penalty) hf
  exact ⟨best, (mem_feasible _ _ _).mp hbest,
    fun other hother => hmaximum other ((mem_feasible _ _ _).mpr hother)⟩

/-- Every pair of finite trees has a nonempty maximum topological witness. -/
theorem exists_maximum (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) : ∃ pairs, IsMaximum left right weights penalty pairs := by
  obtain ⟨u⟩ := left.isTree.connected.nonempty
  obtain ⟨v⟩ := right.isTree.connected.nonempty
  exact exists_maximum_of_feasible left right weights penalty ⟨{(u,v)}, singleton_valid left right u v⟩

omit [Fintype V] [Fintype W] in
/-- The independently defined optimum is nonincreasing in the finite penalty. -/
theorem maximum_score_antitone (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (first second : ℝ) (h : first ≤ second) (firstPairs secondPairs : Mapping V W)
    (hf : IsMaximum left right weights first firstPairs)
    (hs : IsMaximum left right weights second secondPairs) :
    score left right weights second secondPairs ≤ score left right weights first firstPairs :=
  (score_antitone left right weights first second h secondPairs).trans (hf.2 secondPairs hs.1)

end SubtreeProofs.Droschinsky2018

end
