module

public import SubtreeProofs.Droschinsky2018.Reconstruction
public import SubtreeProofs.Shared.GraftedEmbedding
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-!
# Exact scores for a grafted abstract common tree

The sum is over actual abstract vertices and unordered edges. Root connectors
and branch edges are disjoint, so no common edge or vertex is counted twice.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

open Droschinsky2016

variable {I : Type*} {A : I → Type*} [Fintype I] [∀ i, Fintype (A i)]

/-- The abstract edge enumeration agrees with the concrete graft construction. -/
theorem commonEdges_graft (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) :
    commonEdges (TreeGraft.tree trees roots) = TreeGraft.edges trees roots := by
  classical
  ext edge
  rw [commonEdges, SimpleGraph.mem_edgeFinset]
  change edge ∈ (TreeGraft.graph trees roots).edgeSet ↔ _
  rw [TreeGraft.edgeSet_eq]
  rfl

/-- Every additive edge contribution decomposes over new-root connectors and
original branch edges. -/
theorem graft_edge_sum {M : Type*} [AddCommMonoid M] (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    (f : Sym2 (TreeGraft.Vertex A) → M) :
    ∑ edge ∈ TreeGraft.edges trees roots, f edge =
      ∑ i, (f s(none, TreeGraft.branchVertex i (roots i)) +
        ∑ edge ∈ commonEdges (trees i), f (edge.map (TreeGraft.branchVertex i))) := by
  classical
  rw [TreeGraft.edges, Finset.sum_union (TreeGraft.connectors_disjoint trees roots),
    TreeGraft.connectors, Finset.sum_image (fun i _ j _ he => TreeGraft.connector_injective roots he),
    TreeGraft.branches, Finset.sum_biUnion (fun i _ j _ hn => TreeGraft.branchEdges_disjoint trees hn),
    Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [TreeGraft.branchEdges, Finset.sum_image]
  · rfl
  · exact fun a _ b _ he => Sym2.map.injective (TreeGraft.branchVertex_injective i) he

omit [IsStrictOrderedRing K] in
/-- A grafted realization's score is its mapped-root reward plus one
path-and-continuation reward for each attached common branch. -/
theorem realizationScore_graft {V W : Type*} [DecidableEq V] [DecidableEq W]
    (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) {left : FiniteTree V} {right : FiniteTree W}
    (first : TopologicalEmbedding (TreeGraft.tree trees roots) left)
    (second : TopologicalEmbedding (TreeGraft.tree trees roots) right)
    (weights : Scoring V W K) (penalty : WithTop K) :
    realizationScore first second weights penalty = weights.node (first.map none) (second.map none) +
      ∑ i, (pathScore left right weights penalty
          s(first.map none, first.map (TreeGraft.branchVertex i (roots i)))
          s(second.map none, second.map (TreeGraft.branchVertex i (roots i))) +
        realizationScore
          (first.precomposeHom (TreeGraft.includeHom trees roots i) (TreeGraft.branchVertex_injective i))
          (second.precomposeHom (TreeGraft.includeHom trees roots i) (TreeGraft.branchVertex_injective i)) weights penalty) := by
  classical
  unfold realizationScore
  rw [Fintype.sum_option, Fintype.sum_sigma, commonEdges_graft, graft_edge_sum]
  simp only [Finset.sum_add_distrib, Sym2.map_map, Sym2.map_mk]
  dsimp only [TopologicalEmbedding.precomposeHom, Function.comp_def, TreeGraft.includeHom]
  ac_rfl

end SubtreeProofs.Droschinsky2018

end
