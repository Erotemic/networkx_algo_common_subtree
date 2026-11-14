module

public import SubtreeProofs.Droschinsky2018.BoundaryStates

/-!
# Concrete rooted realizations carrying their common top pair

Boundary witnesses have a specified first mapped pair. The realization keeps
that pair as its common root and recovers exactly the original mapping and
score. This is the data used when assembling independently selected branches.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

structure PointedWitness (left : FiniteTree V) (right : FiniteTree W) (leftBase : V) (rightBase : W)
    (pairs : Mapping V W) (top : V × W) where
  source : FiniteTree (LeftVertices pairs)
  root : LeftVertices pairs
  first : RootedTopologicalEmbedding source left root leftBase
  second : RootedTopologicalEmbedding source right root rightBase
  root_left : first.map root = top.1
  root_right : second.map root = top.2
  pairs_eq : pairedImage first.toUnrooted second.toUnrooted = pairs

/-- Every independently valid boundary witness has a concrete pointed realization. -/
theorem StateValid.exists_pointed {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) :
    Nonempty (PointedWitness left right leftBase rightBase pairs top) := by
  obtain ⟨root, hl, hr⟩ := (h.1.embedding_pairs top.1 top.2).mp h.2.1
  have hlTop (a : LeftVertices pairs) :
      left.Ancestor leftBase (h.1.leftEmbedding.map root) (h.1.leftEmbedding.map a) := by
    rw [hl]
    exact (h.2.2.1 (h.1.leftEmbedding.map a, h.1.rightEmbedding.map a)
      ((h.1.embedding_pairs _ _).mpr ⟨a, rfl, rfl⟩)).1
  have hrTop (a : LeftVertices pairs) :
      right.Ancestor rightBase (h.1.rightEmbedding.map root) (h.1.rightEmbedding.map a) := by
    rw [hr]
    exact (h.2.2.1 (h.1.leftEmbedding.map a, h.1.rightEmbedding.map a)
      ((h.1.embedding_pairs _ _).mpr ⟨a, rfl, rfl⟩)).2
  refine ⟨⟨h.1.commonTree, root, h.1.leftEmbedding.toRootedAt root leftBase hlTop,
    h.1.rightEmbedding.toRootedAt root rightBase hrTop, hl, hr, ?_⟩⟩
  change pairedImage h.1.leftEmbedding h.1.rightEmbedding = pairs
  exact h.1.realizations_roundtrip

noncomputable def StateValid.pointed {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) :
    PointedWitness left right leftBase rightBase pairs top := Classical.choice h.exists_pointed

namespace PointedWitness

variable {left : FiniteTree V} {right : FiniteTree W} {leftBase u : V} {rightBase v : W}
  {pairs : Mapping V W} {top : V × W}

omit [Fintype V] [Fintype W] in
/-- The supplied maps select only pairs from the original independent witness. -/
theorem map_pair_mem (witness : PointedWitness left right leftBase rightBase pairs top)
    (a : LeftVertices pairs) : (witness.first.map a, witness.second.map a) ∈ pairs := by
  have hm := (mem_pairedImage witness.first.toUnrooted witness.second.toUnrooted
    (witness.first.map a) (witness.second.map a)).mpr ⟨a, rfl, rfl⟩
  rw [witness.pairs_eq] at hm
  exact hm

omit [Fintype V] [Fintype W] in
/-- Boundary containment transfers to every vertex of the realized common tree. -/
theorem boundary_region (witness : PointedWitness left right leftBase rightBase pairs top)
    (h : StateValid left right leftBase rightBase u v pairs top) (a : LeftVertices pairs) :
    left.Ancestor leftBase u (witness.first.map a) ∧ right.Ancestor rightBase v (witness.second.map a) := by
  have htop := h.2.2.1 _ (witness.map_pair_mem a)
  exact ⟨left.ancestor_trans h.2.2.2.1 htop.1, right.ancestor_trans h.2.2.2.2 htop.2⟩

omit [Fintype V] [Fintype W] in
/-- Pointing and realizing the common root preserves the full internal score. -/
theorem score_eq (witness : PointedWitness left right leftBase rightBase pairs top)
    (weights : Scoring V W) (penalty : WithTop ℝ) :
    realizationScore witness.first.toUnrooted witness.second.toUnrooted weights penalty =
      score left right weights penalty pairs := by
  rw [← score_pairedImage, witness.pairs_eq]

end PointedWitness

end SubtreeProofs.Droschinsky2018

end
