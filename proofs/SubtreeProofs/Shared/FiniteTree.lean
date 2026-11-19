module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Basic

/-!
# Finite-tree problem carriers

Tree vertices, adjacency and unique paths are independent of Rust graph
representations and all dynamic programs. Label-dependent weights are supplied
separately by the paper-specific problem specifications.
-/

@[expose] public section

namespace SubtreeProofs

/-- A tree on a finite vertex type, represented by Mathlib adjacency and its
connected/acyclic invariant. Finiteness is supplied by consumers. -/
structure FiniteTree (V : Type*) where
  graph : SimpleGraph V
  isTree : graph.IsTree

namespace FiniteTree

variable {V : Type*} (tree : FiniteTree V)

/-- The canonical unique simple path, selected from Mathlib's tree theorem. -/
noncomputable def path (first second : V) : tree.graph.Path first second :=
  ⟨(tree.isTree.existsUnique_path first second).choose,
    (tree.isTree.existsUnique_path first second).choose_spec.1⟩

/-- Every pair of tree vertices has exactly one simple path. -/
theorem existsUnique_path (first second : V) :
    ∃! path : tree.graph.Walk first second, path.IsPath :=
  tree.isTree.existsUnique_path first second

/-- No two distinct simple paths can realize the same pair of endpoints. -/
theorem path_unique {first second : V} (p q : tree.graph.Path first second) : p = q :=
  (tree.isTree.isAcyclic.subsingleton_path first second).elim p q

/-- The unique-path length and vertex set used by path-embedding objectives. -/
noncomputable def pathLength (first second : V) : Nat := (tree.path first second).val.length

noncomputable def pathVertices [DecidableEq V] (first second : V) : Finset V :=
  (tree.path first second).val.support.toFinset

noncomputable def pathInterior [DecidableEq V] (first second : V) : Finset V :=
  ((tree.pathVertices first second).erase first).erase second

/-- Canonical paths reverse when their endpoints are swapped. -/
theorem path_reverse (first second : V) : (tree.path first second).reverse = tree.path second first :=
  (tree.isTree.isAcyclic.subsingleton_path second first).elim _ _

theorem pathLength_comm (first second : V) : tree.pathLength first second = tree.pathLength second first := by
  have h := congrArg (fun p : tree.graph.Path second first => p.val.length) (tree.path_reverse first second)
  simpa only [pathLength, SimpleGraph.Path.reverse, SimpleGraph.Walk.length_reverse] using h

theorem pathVertices_comm [DecidableEq V] (first second : V) :
    tree.pathVertices first second = tree.pathVertices second first := by
  have h := congrArg (fun p : tree.graph.Path second first => p.val.support.toFinset) (tree.path_reverse first second)
  simpa only [pathVertices, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse, List.toFinset_reverse] using h

theorem pathInterior_comm [DecidableEq V] (first second : V) :
    tree.pathInterior first second = tree.pathInterior second first := by
  unfold pathInterior
  rw [pathVertices_comm]
  ext vertex
  simp only [Finset.mem_erase]
  tauto

theorem pathLength_pos {first second : V} (hne : first ≠ second) : 0 < tree.pathLength first second := by
  have hzero : tree.pathLength first second ≠ 0 := by
    intro h
    exact hne (SimpleGraph.Walk.eq_of_length_eq_zero h)
  omega

end FiniteTree
end SubtreeProofs

end
