module

public import SubtreeProofs.Droschinsky2018.Specification
public import SubtreeProofs.Droschinsky2016.Witness
public import SubtreeProofs.Shared.TopologicalEmbedding

/-!
# Skeleton witnesses give explicit common-tree realizations

The common tree has the selected left vertices as its carrier. Its two maps
are injective, realize every edge by a positive-length target path, avoid all
mapped vertices in edge interiors and keep distinct edge interiors disjoint.
The rooted source clauses follow by lifting paths. The converse source
correspondence and fixed ambient-root restrictions remain separate obligations.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The selected skeletons are actual isomorphic trees. -/
noncomputable def Valid.skeletonIso {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) :
    skeleton left (pairs.image Prod.fst) ≃g skeleton right (pairs.image Prod.snd) where
  toEquiv := Equiv.ofBijective (witnessMap pairs) (witnessMap_bijective pairs h.2.1)
  map_rel_iff' := by
    intro first second
    change BranchAdjacent right (pairs.image Prod.snd) (pairAtLeft pairs first).2
        (pairAtLeft pairs second).2 ↔
      BranchAdjacent left (pairs.image Prod.fst) first.val second.val
    have ha := h.2.2.2.2.2.2 (pairAtLeft pairs first) (pairAtLeft_mem _ _)
      (pairAtLeft pairs second) (pairAtLeft_mem _ _)
    simpa only [pairAtLeft_fst] using ha.symm

/-- Inclusion of a valid skeleton into its ambient tree is an explicit
topological realization, with no hidden recurrence assumptions. -/
noncomputable def skeletonEmbedding (tree : FiniteTree V) (selected : Finset V)
    (ht : (skeleton tree selected).IsTree) (hd : InteriorDisjoint tree selected) :
    TopologicalEmbedding (FiniteTree.mk (skeleton tree selected) ht) tree where
  map := Subtype.val
  injective := Subtype.val_injective
  avoids_vertices := by
    intro a b hab c hc
    exact Finset.disjoint_left.mp hab.2 hc c.property
  interior_disjoint := by
    classical
    intro a b hab c d hcd hn
    apply hd s(a.val,b.val) ?_ s(c.val,d.val) ?_
    · intro he
      exact hn (Sym2.map.injective Subtype.val_injective he)
    · rw [skeletonEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
      exact ⟨⟨a.property, b.property⟩, hab⟩
    · rw [skeletonEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
      exact ⟨⟨c.property, d.property⟩, hcd⟩

/-- The explicit common tree extracted from an independent pair witness. -/
noncomputable def Valid.commonTree {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) : FiniteTree (LeftVertices pairs) :=
  ⟨skeleton left (pairs.image Prod.fst), h.2.2.1⟩

noncomputable def Valid.leftEmbedding {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) : TopologicalEmbedding h.commonTree left :=
  skeletonEmbedding left (pairs.image Prod.fst) h.2.2.1 h.2.2.2.2.1

noncomputable def Valid.rightEmbedding {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) : TopologicalEmbedding h.commonTree right :=
  (skeletonEmbedding right (pairs.image Prod.snd) h.2.2.2.1 h.2.2.2.2.2.1).precompose h.skeletonIso

/-- Both realizations recover exactly the original finite pair relation. -/
theorem Valid.embedding_pairs {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (x : V) (y : W) :
    (x,y) ∈ pairs ↔ ∃ vertex : LeftVertices pairs,
      h.leftEmbedding.map vertex = x ∧ h.rightEmbedding.map vertex = y := by
  constructor
  · intro hp
    let vertex : LeftVertices pairs := ⟨x, Finset.mem_image.mpr ⟨(x,y), hp, rfl⟩⟩
    refine ⟨vertex, rfl, ?_⟩
    change (pairAtLeft pairs vertex).2 = y
    have he := h.2.1.1 _ (pairAtLeft_mem pairs vertex) (x,y) hp (pairAtLeft_fst pairs vertex)
    exact congrArg Prod.snd he
  · rintro ⟨vertex, hx, hy⟩
    change vertex.val = x at hx
    change (pairAtLeft pairs vertex).2 = y at hy
    have hp := pairAtLeft_mem pairs vertex
    have he : pairAtLeft pairs vertex = (x,y) := Prod.ext ((pairAtLeft_fst pairs vertex).trans hx) hy
    exact he ▸ hp

/-- A selected common root gives two root-to-root embeddings satisfying both
clauses of 2018 Definition 1, with exactly the original mapped vertex pairs. -/
theorem Valid.rooted_realizations {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root : LeftVertices pairs) :
    ∃ (first : RootedTopologicalEmbedding h.commonTree left root (h.leftEmbedding.map root))
      (second : RootedTopologicalEmbedding h.commonTree right root (h.rightEmbedding.map root)),
      first.RootToRoot ∧ second.RootToRoot ∧
        ∀ x y, (x,y) ∈ pairs ↔ ∃ vertex, first.map vertex = x ∧ second.map vertex = y := by
  exact ⟨h.leftEmbedding.toRooted root, h.rightEmbedding.toRooted root, rfl, rfl, h.embedding_pairs⟩

end SubtreeProofs.Droschinsky2018

end
