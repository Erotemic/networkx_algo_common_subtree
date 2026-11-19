module

public import SubtreeProofs.Droschinsky2018.GraftScore
public import SubtreeProofs.Shared.RootedDecomposition

/-!
# Score decomposition for every explicit common-tree witness

The common tree is isomorphic to the graft of its child regions. Reindexing
preserves the finite pair relation and score, so the graft score identity now
applies to arbitrary common-tree witnesses.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018.ScoreDecomposition

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

open Droschinsky2016

variable {A V W : Type*} [Fintype A] [DecidableEq A] [DecidableEq V] [DecidableEq W]
  (common : FiniteTree A) (root : A) {left : FiniteTree V} {right : FiniteTree W}

attribute [local instance] Classical.propDecidable

noncomputable def branch (first : TopologicalEmbedding common left) (c : RootedDecomposition.Index common root) :
    TopologicalEmbedding (RootedDecomposition.branches common root c) left :=
  first.precomposeHom (common.descendantHom root c.val) Subtype.val_injective

noncomputable def pulled (first : TopologicalEmbedding common left) :
    TopologicalEmbedding (RootedDecomposition.graft common root) left :=
  first.precompose (RootedDecomposition.iso common root)

theorem pulled_root (first : TopologicalEmbedding common left) : (pulled common root first).map none = first.map root := rfl

theorem pulled_branch_root (first : TopologicalEmbedding common left) (c : RootedDecomposition.Index common root) :
    (pulled common root first).map (TreeGraft.branchVertex c (RootedDecomposition.branchRoots common root c)) = first.map c.val := rfl

theorem pulled_restrict (first : TopologicalEmbedding common left) (c : RootedDecomposition.Index common root) :
    (pulled common root first).precomposeHom
      (TreeGraft.includeHom (RootedDecomposition.branches common root) (RootedDecomposition.branchRoots common root) c)
      (TreeGraft.branchVertex_injective (A := RootedDecomposition.Carrier common root) c) = branch common root first c := by
  apply TopologicalEmbedding.ext
  funext a
  rfl

omit [IsStrictOrderedRing K] in
/-- Exact root/branch score partition of an arbitrary common-tree realization. -/
theorem score_decomposition (first : TopologicalEmbedding common left) (second : TopologicalEmbedding common right)
    (weights : Scoring V W K) (penalty : WithTop K) :
    realizationScore first second weights penalty = weights.node (first.map root) (second.map root) +
      ∑ c : RootedDecomposition.Index common root,
        (pathScore left right weights penalty s(first.map root, first.map c.val) s(second.map root, second.map c.val) +
          realizationScore (branch common root first c) (branch common root second c) weights penalty) := by
  calc
    _ = realizationScore (pulled common root first) (pulled common root second) weights penalty :=
      (realizationScore_precomposeIso (RootedDecomposition.graft common root)
        (RootedDecomposition.iso common root) first second weights penalty).symm
    _ = _ := by
      have hs := realizationScore_graft (RootedDecomposition.branches common root) (RootedDecomposition.branchRoots common root)
        (pulled common root first) (pulled common root second) weights penalty
      refine hs.trans ?_
      rw [pulled_root, pulled_root]
      congr 1

end SubtreeProofs.Droschinsky2018.ScoreDecomposition

end
