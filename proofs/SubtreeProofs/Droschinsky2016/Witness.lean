module

public import SubtreeProofs.Droschinsky2016.Specification

/-!
# Concrete mapping witnesses are subtree isomorphisms

The finite vertex-pair definition is related to Mathlib's actual induced-graph
isomorphisms. This bridge preserves adjacency in both directions and proves
that connected selected subtrees remain trees.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

abbrev LeftVertices (pairs : Mapping V W) := ↑(↑(pairs.image Prod.fst) : Set V)
abbrev RightVertices (pairs : Mapping V W) := ↑(↑(pairs.image Prod.snd) : Set W)

/-- Pick the pair having a specified selected left endpoint. -/
noncomputable def pairAtLeft (pairs : Mapping V W) (vertex : LeftVertices pairs) : V × W :=
  (Finset.mem_image.mp vertex.property).choose

omit [Fintype V] [Fintype W] [DecidableEq W] in
theorem pairAtLeft_mem (pairs : Mapping V W) (vertex : LeftVertices pairs) :
    pairAtLeft pairs vertex ∈ pairs := (Finset.mem_image.mp vertex.property).choose_spec.1

omit [Fintype V] [Fintype W] [DecidableEq W] in
theorem pairAtLeft_fst (pairs : Mapping V W) (vertex : LeftVertices pairs) :
    (pairAtLeft pairs vertex).1 = vertex.val := (Finset.mem_image.mp vertex.property).choose_spec.2

/-- A pair witness determines a map between its two selected vertex types. -/
noncomputable def witnessMap (pairs : Mapping V W) (vertex : LeftVertices pairs) : RightVertices pairs :=
  ⟨(pairAtLeft pairs vertex).2, Finset.mem_image.mpr ⟨pairAtLeft pairs vertex, pairAtLeft_mem _ _, rfl⟩⟩

omit [Fintype V] [Fintype W] in
theorem witnessMap_bijective (pairs : Mapping V W) (h : PartialBijection pairs) :
    Function.Bijective (witnessMap pairs) := by
  constructor
  · intro first second heq
    have hright := congrArg Subtype.val heq
    change (pairAtLeft pairs first).2 = (pairAtLeft pairs second).2 at hright
    have hp := h.2 _ (pairAtLeft_mem _ _) _ (pairAtLeft_mem _ _) hright
    apply Subtype.ext
    have hleft := congrArg Prod.fst hp
    simpa only [pairAtLeft_fst] using hleft
  · intro vertex
    obtain ⟨pair, hpair, hright⟩ := Finset.mem_image.mp vertex.property
    let first : LeftVertices pairs := ⟨pair.1, Finset.mem_image.mpr ⟨pair, hpair, rfl⟩⟩
    refine ⟨first, ?_⟩
    have heq := h.1 _ (pairAtLeft_mem pairs first) pair hpair (pairAtLeft_fst pairs first)
    apply Subtype.ext
    change (pairAtLeft pairs first).2 = vertex.val
    rw [heq, hright]

omit [Fintype V] [Fintype W] in
/-- A valid finite witness induces an honest graph isomorphism of the selected subtrees. -/
noncomputable def Valid.inducedIso {left : FiniteTree V} {right : FiniteTree W} {pairs : Mapping V W}
    (h : Valid left right pairs) :
    left.graph.induce (↑(pairs.image Prod.fst) : Set V) ≃g
      right.graph.induce (↑(pairs.image Prod.snd) : Set W) where
  toEquiv := Equiv.ofBijective (witnessMap pairs) (witnessMap_bijective pairs h.2.1)
  map_rel_iff' := by
    intro first second
    change right.graph.Adj (pairAtLeft pairs first).2 (pairAtLeft pairs second).2 ↔
      left.graph.Adj first.val second.val
    have hadj := h.2.2.2.2 (pairAtLeft pairs first) (pairAtLeft_mem pairs first)
      (pairAtLeft pairs second) (pairAtLeft_mem pairs second)
    simpa only [pairAtLeft_fst] using hadj.symm

omit [Fintype V] [Fintype W] in
/-- The selected left common object is a tree, not merely connected. -/
theorem Valid.left_isTree {left : FiniteTree V} {right : FiniteTree W} {pairs : Mapping V W}
    (h : Valid left right pairs) :
    (left.graph.induce (↑(pairs.image Prod.fst) : Set V)).IsTree :=
  ⟨h.2.2.1, left.isTree.isAcyclic.induce _⟩

omit [Fintype V] [Fintype W] in
/-- The selected right common object is a tree as well. -/
theorem Valid.right_isTree {left : FiniteTree V} {right : FiniteTree W} {pairs : Mapping V W}
    (h : Valid left right pairs) :
    (right.graph.induce (↑(pairs.image Prod.snd) : Set W)).IsTree :=
  ⟨h.2.2.2.1, right.isTree.isAcyclic.induce _⟩

end SubtreeProofs.Droschinsky2016

end
