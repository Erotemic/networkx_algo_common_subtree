module

public import SubtreeProofs.Shared.FiniteTree
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Tactic

/-!
# Independent weighted common-subtree-isomorphism problem

A witness is a nonempty finite partial bijection between connected induced
subtrees and preserves adjacency in both directions. Unordered edge pairs are
summed once using `Sym2`, without choosing a vertex order. Weights use `WithBot K`
for an ordered ring `K`, instantiated by real paper scores or exact integers.
The source's negative infinity and negative optima remain visible. The
empty-allowed implementation convention is a separate predicate.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- A finite concrete vertex-pair witness. -/
abbrev Mapping (V W : Type*) := Finset (V × W)

/-- Injectivity on both projections makes a mapping a partial bijection. -/
def PartialBijection (pairs : Mapping V W) : Prop :=
  (∀ p ∈ pairs, ∀ q ∈ pairs, p.1 = q.1 → p = q) ∧
  (∀ p ∈ pairs, ∀ q ∈ pairs, p.2 = q.2 → p = q)

/-- Source-faithful structural witness, with a nonempty connected common tree. -/
def Valid (left : FiniteTree V) (right : FiniteTree W) (pairs : Mapping V W) : Prop :=
  pairs.Nonempty ∧ PartialBijection pairs ∧
    (left.graph.induce (↑(pairs.image Prod.fst) : Set V)).Connected ∧
    (right.graph.induce (↑(pairs.image Prod.snd) : Set W)).Connected ∧
    ∀ p ∈ pairs, ∀ q ∈ pairs, left.graph.Adj p.1 q.1 ↔ right.graph.Adj p.2 q.2

/-- Explicit optional-empty API convention, kept distinct from the source problem. -/
def ValidOrEmpty (left : FiniteTree V) (right : FiniteTree W) (pairs : Mapping V W) : Prop :=
  pairs = ∅ ∨ Valid left right pairs

/-- Label or vertex-pair rewards, including source negative infinity. -/
structure Scoring (V W K : Type*) where
  node : V → W → WithBot K
  edge : Sym2 V → Sym2 W → WithBot K

/-- Adjacency of the left endpoints is well-defined on an unordered pair. -/
def mappedAdj (left : FiniteTree V) : Sym2 (V × W) → Prop :=
  Sym2.lift ⟨fun p q => left.graph.Adj p.1 q.1,
    fun p q => propext (left.graph.adj_comm p.1 q.1)⟩

/-- Every abstract common edge appears once, with diagonal pairs excluded by
loop-free adjacency. The induced-edge preservation condition validates the right side. -/
noncomputable def mappedEdges (left : FiniteTree V) (pairs : Mapping V W) : Finset (Sym2 (V × W)) := by
  classical
  exact pairs.sym2.filter (mappedAdj left)

/-- Independent score: each selected vertex and each unordered common edge once. -/
noncomputable def score (left : FiniteTree V) (weights : Scoring V W K) (pairs : Mapping V W) : WithBot K :=
  (∑ p ∈ pairs, weights.node p.1 p.2) +
    ∑ e ∈ mappedEdges left pairs, weights.edge (e.map Prod.fst) (e.map Prod.snd)

/-- Source optimum, with no recurrence or implementation in its definition. -/
def IsMaximum (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W K)
    (pairs : Mapping V W) : Prop :=
  Valid left right pairs ∧ ∀ other, Valid left right other → score left weights other ≤ score left weights pairs


omit [Fintype V] [Fintype W] in
/-- A one-vertex common subtree is always a structural witness, even if its
weight is negative or negative infinity. -/
theorem singleton_valid (left : FiniteTree V) (right : FiniteTree W) (u : V) (v : W) :
    Valid left right {(u,v)} := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · simp [PartialBijection]
  · have hset : ({(u,v)} : Mapping V W).image Prod.fst = {u} := Finset.image_singleton _ _
    rw [hset, Finset.coe_singleton]
    exact SimpleGraph.Connected.of_subsingleton
  · have hset : ({(u,v)} : Mapping V W).image Prod.snd = {v} := Finset.image_singleton _ _
    rw [hset, Finset.coe_singleton]
    exact SimpleGraph.Connected.of_subsingleton
  · intro p hp q hq
    have hp' := Finset.mem_singleton.mp hp
    have hq' := Finset.mem_singleton.mp hq
    subst p
    subst q
    simp


omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- A singleton has no abstract edges; diagonal pairs are never rewarded. -/
@[simp] theorem mappedEdges_singleton (left : FiniteTree V) (u : V) (v : W) :
    mappedEdges left {(u,v)} = ∅ := by
  classical
  rw [mappedEdges, Finset.sym2_singleton]
  apply Finset.filter_eq_empty_iff.mpr
  intro edge he
  have heq := Finset.mem_singleton.mp he
  subst edge
  change ¬ left.graph.Adj u u
  simp

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [LinearOrder K] [IsStrictOrderedRing K] in
/-- The source singleton score can be negative; it is not clamped to zero. -/
@[simp] theorem score_singleton (left : FiniteTree V) (weights : Scoring V W K) (u : V) (v : W) :
    score left weights {(u,v)} = weights.node u v := by
  simp [score]

/-- The finite feasible family, independent of any matching/tree algorithm. -/
noncomputable def feasible (left : FiniteTree V) (right : FiniteTree W) : Finset (Mapping V W) := by
  classical
  exact (Finset.univ.powerset).filter (Valid left right)

@[simp] theorem mem_feasible (left : FiniteTree V) (right : FiniteTree W) (pairs : Mapping V W) :
    pairs ∈ feasible left right ↔ Valid left right pairs := by
  classical
  simp [feasible]

omit [IsStrictOrderedRing K] in
/-- Every structurally feasible pair of trees has an attained optimum over its
finite witness family. No zero clamp or sign hypothesis is needed. -/
theorem exists_maximum_of_feasible (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W K)
    (h : ∃ pairs, Valid left right pairs) : ∃ pairs, IsMaximum left right weights pairs := by
  classical
  obtain ⟨pairs, hpairs⟩ := h
  have hf : (feasible left right).Nonempty := ⟨pairs, (mem_feasible _ _ _).mpr hpairs⟩
  obtain ⟨best, hbest, hmaximum⟩ := Finset.exists_max_image (feasible left right) (score left weights) hf
  exact ⟨best, (mem_feasible _ _ _).mp hbest,
    fun other hother => hmaximum other ((mem_feasible _ _ _).mpr hother)⟩

omit [IsStrictOrderedRing K] in
/-- The source optimum is attained for every pair of finite trees, without an
extra feasibility or positivity hypothesis. -/
theorem exists_maximum (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W K) :
    ∃ pairs, IsMaximum left right weights pairs := by
  obtain ⟨u⟩ := left.isTree.connected.nonempty
  obtain ⟨v⟩ := right.isTree.connected.nonempty
  exact exists_maximum_of_feasible left right weights ⟨{(u,v)}, singleton_valid left right u v⟩

end SubtreeProofs.Droschinsky2016

end
