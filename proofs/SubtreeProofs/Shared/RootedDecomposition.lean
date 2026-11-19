module

public import SubtreeProofs.Shared.GraftedEmbedding

/-!
# Every finite rooted tree is a graft of its child-descendant subtrees

The decomposition is an explicit graph isomorphism. It supplies the inverse
of common-tree assembly when proving that an arbitrary mapped-root embedding
is bounded by the child matching recurrence.
-/

@[expose] public section

namespace SubtreeProofs.FiniteTree

variable {V : Type*} (tree : FiniteTree V)

abbrev Descendant (root c : V) : Type _ := {a : V // tree.Ancestor root c a}

noncomputable def descendantsTree (root c : V) : FiniteTree (tree.Descendant root c) where
  graph := tree.graph.induce {a | tree.Ancestor root c a}
  isTree := ⟨by
    apply tree.connected_of_path_closed (selected := {a | tree.Ancestor root c a})
      ⟨c, tree.ancestor_refl _ _⟩
    intro a ha b hb x hx
    exact tree.descendant_path_closed ha hb x hx,
    tree.isTree.isAcyclic.induce _⟩

def descendantRoot (root c : V) : tree.Descendant root c := ⟨c, tree.ancestor_refl _ _⟩

def descendantHom (root c : V) : (tree.descendantsTree root c).graph →g tree.graph :=
  ⟨Subtype.val, fun ha => ha⟩

end SubtreeProofs.FiniteTree

namespace SubtreeProofs.RootedDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V] (tree : FiniteTree V) (root : V)

attribute [local instance] Classical.propDecidable

noncomputable def children : Finset V := Finset.univ.filter (tree.graph.Adj root)

omit [DecidableEq V] in
@[simp] theorem mem_children (c : V) : c ∈ children tree root ↔ tree.graph.Adj root c := by
  simp [children]

abbrev Index : Type _ := ↑(children tree root)
abbrev Carrier (c : Index tree root) : Type _ := tree.Descendant root c.val

noncomputable def branches (c : Index tree root) : FiniteTree (Carrier tree root c) := tree.descendantsTree root c.val

def branchRoots (c : Index tree root) : Carrier tree root c := tree.descendantRoot root c.val

noncomputable def graft : FiniteTree (TreeGraft.Vertex (Carrier tree root)) :=
  TreeGraft.tree (branches tree root) (branchRoots tree root)

noncomputable def branchEmbedding (c : Index tree root) :
    RootedTopologicalEmbedding (branches tree root c) tree (branchRoots tree root c) root :=
  (TopologicalEmbedding.ofHom (tree.descendantHom root c.val) Subtype.val_injective).toRootedAt
    (branchRoots tree root c) root (fun a => a.property)

noncomputable def realization : RootedTopologicalEmbedding (graft tree root) tree none root :=
  GraftedEmbedding.embedding root (branchEmbedding tree root) (fun c => c.val) Subtype.val_injective
    (fun c => ⟨(mem_children tree root c.val).mp c.property, tree.root_ancestor _ _⟩)
    (fun _ a => a.property)

omit [DecidableEq V] in
theorem root_child (c : Index tree root) : tree.Child root root c.val :=
  ⟨(mem_children tree root c.val).mp c.property, tree.root_ancestor _ _⟩

/-- Flatten a graft vertex back to its original tree vertex. -/
def unpack : TreeGraft.Vertex (Carrier tree root) → V
  | none => root
  | some ⟨_,a⟩ => a.val

theorem realization_map (p : TreeGraft.Vertex (Carrier tree root)) :
    (realization tree root).map p = unpack tree root p := by
  cases p with
  | none => rfl
  | some p => rcases p with ⟨i,a⟩; rfl

theorem unpack_injective : Function.Injective (unpack tree root) := by
  intro p q he
  apply (realization tree root).injective
  rw [realization_map, realization_map]
  exact he

theorem unpack_surjective : Function.Surjective (unpack tree root) := by
  intro a
  by_cases he : a = root
  · exact ⟨none, he.symm⟩
  · let c := tree.firstChild root a
    have hc : tree.graph.Adj root c := tree.firstChild_adj (fun h => he h.symm)
    let index : Index tree root := ⟨c, (mem_children tree root c).mpr hc⟩
    let vertex : Carrier tree root index := ⟨a, tree.firstChild_ancestor⟩
    exact ⟨some ⟨index,vertex⟩, rfl⟩

/-- The flattening also preserves actual graph edges, not only paths. -/
def unpackHom : (graft tree root).graph →g tree.graph where
  toFun := unpack tree root
  map_rel' := by
    intro p q hpq
    cases p with
    | none =>
      cases q with
      | none => exact False.elim (hpq.ne rfl)
      | some q =>
        rcases q with ⟨i,a⟩
        have he := (TreeGraft.root_adj_iff (branches tree root) (branchRoots tree root) i a).mp hpq
        change tree.graph.Adj root a.val
        rw [he]
        exact (mem_children tree root i.val).mp i.property
    | some p =>
      rcases p with ⟨i,a⟩
      cases q with
      | none =>
        have he := (TreeGraft.root_adj_iff (branches tree root) (branchRoots tree root) i a).mp hpq.symm
        change tree.graph.Adj a.val root
        rw [he]
        exact ((mem_children tree root i.val).mp i.property).symm
      | some q =>
        rcases q with ⟨j,b⟩
        have hij := TreeGraft.branch_adj_index (branches tree root) (branchRoots tree root) a b hpq
        subst j
        exact (TreeGraft.branch_adj_iff (branches tree root) (branchRoots tree root) i a b).mp hpq

/-- Exact inverse to grafting the rooted child regions of any finite tree. -/
noncomputable def iso : (graft tree root).graph ≃g tree.graph where
  toEquiv := Equiv.ofBijective (unpack tree root) ⟨unpack_injective tree root, unpack_surjective tree root⟩
  map_rel_iff' := by
    intro a b
    exact (graft tree root).adj_map_iff tree (unpackHom tree root) (unpack_injective tree root) a b

end SubtreeProofs.RootedDecomposition

namespace SubtreeProofs.RootedTopologicalEmbedding

variable {A V : Type*} [Fintype A] [DecidableEq A] [DecidableEq V]
  {common : FiniteTree A} {target : FiniteTree V} {commonRoot : A} {targetRoot : V}

/-- The immediate target child region entered by a realized common-child edge. -/
noncomputable def branchChild (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    (c : RootedDecomposition.Index common commonRoot) : V :=
  target.firstChild (embedding.map commonRoot) (embedding.map c.val)

theorem branchChild_valid (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    (c : RootedDecomposition.Index common commonRoot) :
    target.Child targetRoot (embedding.map commonRoot) (embedding.branchChild c) := by
  have hc := RootedDecomposition.root_child common commonRoot c
  have hdown := embedding.downward commonRoot c.val hc
  exact ⟨target.firstChild_adj (fun he => hc.1.ne (embedding.injective he)),
    target.ancestor_of_mem_suffix hdown target.firstChild_ancestor⟩

theorem branchChild_top (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    (c : RootedDecomposition.Index common commonRoot) :
    target.Ancestor targetRoot (embedding.branchChild c) (embedding.map c.val) :=
  target.suffix_ancestor (embedding.downward commonRoot c.val (RootedDecomposition.root_child common commonRoot c))
    target.firstChild_ancestor

theorem branchChild_injective (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot) :
    Function.Injective embedding.branchChild := by
  intro c d he
  apply Subtype.ext
  by_contra hn
  exact embedding.firstChild_ne (RootedDecomposition.root_child common commonRoot c)
    (RootedDecomposition.root_child common commonRoot d) hn he

end SubtreeProofs.RootedTopologicalEmbedding

end
