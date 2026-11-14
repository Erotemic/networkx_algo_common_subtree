module

public import SubtreeProofs.Paper2004.OrderedTree
import Mathlib.Tactic

/-!
# Independent ordered subtree isomorphism contract

Root-preserving selection deletes whole child subtrees and prunes retained
children, preserving their order and every retained parent-child edge. It never
splices grandchildren into the parent's list. General selection may choose its
root at any actual descendant. These relations do not mention balanced words,
contractions or the algorithm. This is a separate project extension, not a
second recurrence stated in the 2004 paper. Vertex-pair sequence APIs require
an additional conversion contract when their outer level represents a forest.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

mutual
  /-- Root-preserving ordered adjacency-preserving subtree selection. -/
  inductive RootPrunes : OrderedTree → OrderedTree → Prop where
    | node {small large} : ForestPrunes small large → RootPrunes (.node small) (.node large)

  /-- Select whole children in order; skipped children promote no descendants. -/
  inductive ForestPrunes : List OrderedTree → List OrderedTree → Prop where
    | nil (large) : ForestPrunes [] large
    | skip {small large} (first) : ForestPrunes small large → ForestPrunes small (first::large)
    | cons {small large restSmall restLarge} : RootPrunes small large →
        ForestPrunes restSmall restLarge → ForestPrunes (small::restSmall) (large::restLarge)
end

mutual
  theorem RootPrunes.edgeCount_le {small large : OrderedTree} (h : RootPrunes small large) :
      small.edgeCount ≤ large.edgeCount := by
    cases h with
    | node forest => exact ForestPrunes.edgeCount_le forest

  theorem ForestPrunes.edgeCount_le {small large : List OrderedTree} (h : ForestPrunes small large) :
      forestEdgeCount small ≤ forestEdgeCount large := by
    cases h with
    | nil => simp only [forestEdgeCount_nil]; omega
    | skip first rest =>
      have hb := ForestPrunes.edgeCount_le rest
      simp only [forestEdgeCount_cons]
      omega
    | cons child rest =>
      have hc := RootPrunes.edgeCount_le child
      have hr := ForestPrunes.edgeCount_le rest
      simp only [forestEdgeCount_cons]
      omega
end

mutual
  theorem RootPrunes.refl (tree : OrderedTree) : RootPrunes tree tree := by
    cases tree with
    | node children => exact .node (ForestPrunes.refl children)

  theorem ForestPrunes.refl (forest : List OrderedTree) : ForestPrunes forest forest := by
    cases forest with
    | nil => exact .nil []
    | cons first rest => exact .cons (RootPrunes.refl first) (ForestPrunes.refl rest)
end

/-- A nonempty selection either skips or keeps the first source child. -/
theorem ForestPrunes.first {child : OrderedTree} {rest : List OrderedTree}
    {first : OrderedTree} {tail : List OrderedTree} (h : ForestPrunes (child::rest) (first::tail)) :
    ForestPrunes (child::rest) tail ∨ RootPrunes child first ∧ ForestPrunes rest tail := by
  cases h with
  | skip _ rest => exact Or.inl rest
  | cons child rest => exact Or.inr ⟨child,rest⟩

theorem ForestPrunes.eq_nil_of_nil {small : List OrderedTree} (h : ForestPrunes small []) : small = [] := by
  cases h
  rfl

theorem RootPrunes.children {small large : OrderedTree} (h : RootPrunes small large) :
    ForestPrunes small.children large.children := by
  cases h with
  | node forest => exact forest

/-- A root reached along zero or more actual child edges. -/
inductive Descendant : OrderedTree → OrderedTree → Prop where
  | refl (tree : OrderedTree) : Descendant tree tree
  | step {root child source : OrderedTree} : child ∈ OrderedTree.children source → Descendant root child → Descendant root source

theorem forest_member_edgeCount_lt {child : OrderedTree} {forest : List OrderedTree} (h : child ∈ forest) :
    child.edgeCount < forestEdgeCount forest := by
  induction forest with
  | nil => cases h
  | cons first rest ih =>
    simp only [List.mem_cons] at h
    simp only [forestEdgeCount_cons]
    rcases h with rfl | h
    · omega
    · have hb := ih h
      omega

theorem Descendant.edgeCount_le {root source : OrderedTree} (h : Descendant root source) :
    root.edgeCount ≤ source.edgeCount := by
  induction h with
  | refl => omega
  | @step child source hmem hpath ih =>
    have hb := forest_member_edgeCount_lt hmem
    cases source
    simp only [children,edgeCount_node] at *
    omega

/-- A connected ordered subtree rooted at any actual input vertex. The score
counts retained edges; the root contributes no virtual incoming edge. -/
def IsomorphicSubtree (small large : OrderedTree) : Prop :=
  ∃ root, Descendant root large ∧ RootPrunes small root

theorem RootPrunes.isomorphicSubtree {small large : OrderedTree} (h : RootPrunes small large) :
    IsomorphicSubtree small large := ⟨large,.refl large,h⟩

theorem IsomorphicSubtree.edgeCount_le {small large : OrderedTree} (h : IsomorphicSubtree small large) :
    small.edgeCount ≤ large.edgeCount := by
  obtain ⟨root,hroot,hprune⟩ := h
  exact hprune.edgeCount_le.trans hroot.edgeCount_le

theorem IsomorphicSubtree.below {small child source : OrderedTree} (h : IsomorphicSubtree small child)
    (hchild : child ∈ source.children) : IsomorphicSubtree small source := by
  obtain ⟨root,hroot,hprune⟩ := h
  exact ⟨root,.step hchild hroot,hprune⟩

/-- Restoring a skipped first child permits the same selected subtree. -/
theorem IsomorphicSubtree.skip {small first : OrderedTree} {tail : List OrderedTree}
    (h : IsomorphicSubtree small (.node tail)) : IsomorphicSubtree small (.node (first::tail)) := by
  obtain ⟨root,hroot,hprune⟩ := h
  cases hroot with
  | refl =>
    cases small with
    | node selected => exact (RootPrunes.node (ForestPrunes.skip first hprune.children)).isomorphicSubtree
  | step hmem hpath => exact ⟨root,.step (List.mem_cons_of_mem first hmem) hpath,hprune⟩

/-- The chosen root is current, in the first child, or in a later child. -/
theorem IsomorphicSubtree.first {small first : OrderedTree} {tail : List OrderedTree}
    (h : IsomorphicSubtree small (.node (first::tail))) :
    RootPrunes small (.node (first::tail)) ∨ IsomorphicSubtree small first ∨ IsomorphicSubtree small (.node tail) := by
  obtain ⟨root,hroot,hprune⟩ := h
  cases hroot with
  | refl => exact Or.inl hprune
  | @step child _ hmem hpath =>
    simp only [children,List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inr (Or.inl ⟨root,hpath,hprune⟩)
    · exact Or.inr (Or.inr ⟨root,.step hmem hpath,hprune⟩)

/-- Independent root-preserving common ordered subtree optimum. -/
def IsMaximumRootedIsomorphism (candidate left right : OrderedTree) : Prop :=
  (RootPrunes candidate left ∧ RootPrunes candidate right) ∧
    ∀ other, RootPrunes other left → RootPrunes other right → other.edgeCount ≤ candidate.edgeCount

/-- Independent maximum common ordered subtree with freely chosen roots. -/
def IsMaximumIsomorphism (candidate left right : OrderedTree) : Prop :=
  (IsomorphicSubtree candidate left ∧ IsomorphicSubtree candidate right) ∧
    ∀ other, IsomorphicSubtree other left → IsomorphicSubtree other right → other.edgeCount ≤ candidate.edgeCount

end SubtreeProofs.Paper2004.OrderedTree

end
