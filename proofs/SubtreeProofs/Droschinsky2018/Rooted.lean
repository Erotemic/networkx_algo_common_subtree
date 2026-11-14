module

public import SubtreeProofs.Droschinsky2018.Reconstruction

/-!
# Fixed ambient-root embedding problem

Rooted admissibility is specified by a shared selected top pair in the two
ambient orientations. This is equivalent to the paper's local source
embeddings with the supplied roots, rather than assumed by an unrooted DP.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- General rooted CSE: the common root need not map to either input root. -/
def RootedValid (left : FiniteTree V) (right : FiniteTree W) (leftRoot : V) (rightRoot : W)
    (pairs : Mapping V W) : Prop :=
  Valid left right pairs ∧ ∃ p ∈ pairs, ∀ q ∈ pairs,
    left.Ancestor leftRoot p.1 q.1 ∧ right.Ancestor rightRoot p.2 q.2

/-- Source root-to-root CSE. This is a separate restriction from general rooted CSE. -/
def RootToRootValid (left : FiniteTree V) (right : FiniteTree W) (leftRoot : V) (rightRoot : W)
    (pairs : Mapping V W) : Prop := Valid left right pairs ∧ (leftRoot,rightRoot) ∈ pairs

theorem RootToRootValid.toRootedValid {left : FiniteTree V} {right : FiniteTree W}
    {leftRoot : V} {rightRoot : W} {pairs : Mapping V W}
    (h : RootToRootValid left right leftRoot rightRoot pairs) :
    RootedValid left right leftRoot rightRoot pairs :=
  ⟨h.1, (leftRoot,rightRoot), h.2, fun _ _ => ⟨left.root_ancestor _ _, right.root_ancestor _ _⟩⟩

theorem rooted_singleton_valid (left : FiniteTree V) (right : FiniteTree W)
    (leftRoot u : V) (rightRoot v : W) : RootedValid left right leftRoot rightRoot {(u,v)} := by
  refine ⟨singleton_valid _ _ _ _, (u,v), by simp, ?_⟩
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  exact ⟨left.ancestor_refl _ _, right.ancestor_refl _ _⟩

/-- Source embeddings with fixed supplied roots yield the shared-top property. -/
theorem source_embeddings_rooted {A : Type*} [Fintype A] {common : FiniteTree A} {root : A}
    {left : FiniteTree V} {right : FiniteTree W} {leftRoot : V} {rightRoot : W}
    (first : RootedTopologicalEmbedding common left root leftRoot)
    (second : RootedTopologicalEmbedding common right root rightRoot) :
    RootedValid left right leftRoot rightRoot (pairedImage first.toUnrooted second.toUnrooted) := by
  refine ⟨pairedImage_valid _ _, (first.map root, second.map root),
    (mem_pairedImage _ _ _ _).mpr ⟨root, rfl, rfl⟩, ?_⟩
  intro q hq
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨first.ancestor_preserved (common.root_ancestor _ _),
    second.ancestor_preserved (common.root_ancestor _ _)⟩

/-- Exact source correspondence for supplied, fixed ambient roots. -/
theorem rootedValid_iff_source_embeddings [Fintype V] [Fintype W]
    (left : FiniteTree V) (right : FiniteTree W) (leftRoot : V) (rightRoot : W) (pairs : Mapping V W) :
    RootedValid left right leftRoot rightRoot pairs ↔
      ∃ (source : FiniteTree (LeftVertices pairs)) (root : LeftVertices pairs)
        (first : RootedTopologicalEmbedding source left root leftRoot)
        (second : RootedTopologicalEmbedding source right root rightRoot),
        pairedImage first.toUnrooted second.toUnrooted = pairs := by
  constructor
  · rintro ⟨h, p, hp, htop⟩
    obtain ⟨root, hl, hr⟩ := (h.embedding_pairs p.1 p.2).mp hp
    have hlTop (a : LeftVertices pairs) :
        left.Ancestor leftRoot (h.leftEmbedding.map root) (h.leftEmbedding.map a) := by
      rw [hl]
      exact (htop (h.leftEmbedding.map a, h.rightEmbedding.map a)
        ((h.embedding_pairs _ _).mpr ⟨a, rfl, rfl⟩)).1
    have hrTop (a : LeftVertices pairs) :
        right.Ancestor rightRoot (h.rightEmbedding.map root) (h.rightEmbedding.map a) := by
      rw [hr]
      exact (htop (h.leftEmbedding.map a, h.rightEmbedding.map a)
        ((h.embedding_pairs _ _).mpr ⟨a, rfl, rfl⟩)).2
    refine ⟨h.commonTree, root, h.leftEmbedding.toRootedAt root leftRoot hlTop,
      h.rightEmbedding.toRootedAt root rightRoot hrTop, ?_⟩
    change pairedImage h.leftEmbedding h.rightEmbedding = pairs
    exact h.realizations_roundtrip
  · rintro ⟨source, root, first, second, he⟩
    rw [← he]
    exact source_embeddings_rooted first second

/-- Exact source correspondence for the separate root-to-root restriction. -/
theorem rootToRootValid_iff_source_embeddings [Fintype V] [Fintype W]
    (left : FiniteTree V) (right : FiniteTree W) (leftRoot : V) (rightRoot : W) (pairs : Mapping V W) :
    RootToRootValid left right leftRoot rightRoot pairs ↔
      ∃ (source : FiniteTree (LeftVertices pairs)) (root : LeftVertices pairs)
        (first : RootedTopologicalEmbedding source left root leftRoot)
        (second : RootedTopologicalEmbedding source right root rightRoot),
        first.RootToRoot ∧ second.RootToRoot ∧ pairedImage first.toUnrooted second.toUnrooted = pairs := by
  constructor
  · rintro ⟨h, hp⟩
    obtain ⟨root, hl, hr⟩ := (h.embedding_pairs leftRoot rightRoot).mp hp
    have hlTop (a : LeftVertices pairs) :
        left.Ancestor leftRoot (h.leftEmbedding.map root) (h.leftEmbedding.map a) := by
      rw [hl]
      exact left.root_ancestor _ _
    have hrTop (a : LeftVertices pairs) :
        right.Ancestor rightRoot (h.rightEmbedding.map root) (h.rightEmbedding.map a) := by
      rw [hr]
      exact right.root_ancestor _ _
    refine ⟨h.commonTree, root, h.leftEmbedding.toRootedAt root leftRoot hlTop,
      h.rightEmbedding.toRootedAt root rightRoot hrTop, hl, hr, ?_⟩
    change pairedImage h.leftEmbedding h.rightEmbedding = pairs
    exact h.realizations_roundtrip
  · rintro ⟨source, root, first, second, hl, hr, he⟩
    rw [← he]
    refine ⟨pairedImage_valid _ _, (mem_pairedImage _ _ _ _).mpr ⟨root, ?_, ?_⟩⟩
    · exact hl
    · exact hr

variable [Fintype V] [Fintype W]

/-- The independent finite family for fixed ambient roots. -/
noncomputable def rootedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftRoot : V) (rightRoot : W) : Finset (Mapping V W) := by
  classical
  exact (Finset.univ.powerset).filter (RootedValid left right leftRoot rightRoot)

@[simp] theorem mem_rootedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftRoot : V) (rightRoot : W) (pairs : Mapping V W) :
    pairs ∈ rootedFeasible left right leftRoot rightRoot ↔ RootedValid left right leftRoot rightRoot pairs := by
  classical
  simp [rootedFeasible]

/-- Independent rooted optimum, with no zero clamp and no recurrence in its definition. -/
noncomputable def rootedValue (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftRoot : V) (rightRoot : W) : WithBot ℝ :=
  (rootedFeasible left right leftRoot rightRoot).sup (score left right weights penalty)

/-- The rooted score maximum is always attained by a nonempty source witness. -/
theorem rootedValue_attained (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftRoot : V) (rightRoot : W) :
    ∃ pairs, RootedValid left right leftRoot rightRoot pairs ∧
      score left right weights penalty pairs = rootedValue left right weights penalty leftRoot rightRoot := by
  have hn : (rootedFeasible left right leftRoot rightRoot).Nonempty :=
    ⟨{(leftRoot,rightRoot)}, (mem_rootedFeasible _ _ _ _ _).mpr (rooted_singleton_valid _ _ _ _ _ _)⟩
  obtain ⟨pairs, hp, hmax⟩ := Finset.exists_max_image
    (rootedFeasible left right leftRoot rightRoot) (score left right weights penalty) hn
  exact ⟨pairs, (mem_rootedFeasible _ _ _ _ _).mp hp,
    le_antisymm (Finset.le_sup (f := score left right weights penalty) hp) (Finset.sup_le hmax)⟩

end SubtreeProofs.Droschinsky2018

end
