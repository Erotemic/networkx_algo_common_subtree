module

public import SubtreeProofs.Droschinsky2018.PointedWitness
public import SubtreeProofs.Droschinsky2018.GraftScore
public import SubtreeProofs.Droschinsky2018.BranchReward

/-!
# Constructive assembly of mapped-root boundary witnesses

A partial matching of immediate input children supplies independent boundary
continuations. Each continuation is realized as an actual common tree; these
trees and their maps are grafted beneath the mapped parent pair.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

structure BoundaryFamily (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) where
  children : Mapping V W
  injective : PartialBijection children
  adjacent : ∀ child ∈ children, left.Child leftBase u child.1 ∧ right.Child rightBase v child.2
  witness : (V × W) → BoundaryWitness V W
  valid : ∀ child ∈ children,
    StateValid left right leftBase rightBase child.1 child.2 (witness child).1 (witness child).2

namespace BoundaryFamily

variable {left : FiniteTree V} {right : FiniteTree W} {leftBase u : V} {rightBase v : W}
  (family : BoundaryFamily left right leftBase rightBase u v)

abbrev Index := ↑family.children
abbrev Carrier (i : family.Index) : Type _ := ↑(LeftVertices (family.witness i.val).1)

noncomputable def pointed (i : family.Index) :
    PointedWitness left right leftBase rightBase (family.witness i.val).1 (family.witness i.val).2 :=
  (family.valid i.val i.property).pointed

noncomputable def trees (i : family.Index) : FiniteTree (family.Carrier i) := (family.pointed i).source
noncomputable def roots (i : family.Index) : family.Carrier i := (family.pointed i).root

noncomputable def first : RootedTopologicalEmbedding (TreeGraft.tree family.trees family.roots) left none leftBase :=
  GraftedEmbedding.embedding u (fun i => (family.pointed i).first) (fun i => i.val.1)
    (fun i j he => Subtype.ext (family.injective.1 i.val i.property j.val j.property he))
    (fun i => (family.adjacent i.val i.property).1)
    (fun i a => ((family.pointed i).boundary_region (family.valid i.val i.property) a).1)

noncomputable def second : RootedTopologicalEmbedding (TreeGraft.tree family.trees family.roots) right none rightBase :=
  GraftedEmbedding.embedding v (fun i => (family.pointed i).second) (fun i => i.val.2)
    (fun i j he => Subtype.ext (family.injective.2 i.val i.property j.val j.property he))
    (fun i => (family.adjacent i.val i.property).2)
    (fun i a => ((family.pointed i).boundary_region (family.valid i.val i.property) a).2)

noncomputable def pairs : Mapping V W := pairedImage family.first.toUnrooted family.second.toUnrooted

/-- The assembled concrete mapping is feasible for the mapped parent state. -/
theorem state_valid : StateValid left right leftBase rightBase u v family.pairs (u,v) := by
  refine ⟨pairedImage_valid _ _, (mem_pairedImage _ _ _ _).mpr ⟨none, rfl, rfl⟩, ?_,
    left.ancestor_refl _ _, right.ancestor_refl _ _⟩
  intro p hp
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨family.first.ancestor_preserved ((TreeGraft.tree family.trees family.roots).root_ancestor none a),
    family.second.ancestor_preserved ((TreeGraft.tree family.trees family.roots).root_ancestor none a)⟩

@[simp] theorem first_root : family.first.map none = u := rfl
@[simp] theorem second_root : family.second.map none = v := rfl

theorem first_branch_root (i : family.Index) :
    family.first.map (TreeGraft.branchVertex i (family.roots i)) = (family.witness i.val).2.1 :=
  (family.pointed i).root_left

theorem second_branch_root (i : family.Index) :
    family.second.map (TreeGraft.branchVertex i (family.roots i)) = (family.witness i.val).2.2 :=
  (family.pointed i).root_right

theorem first_restrict (i : family.Index) :
    family.first.toUnrooted.precomposeHom (TreeGraft.includeHom family.trees family.roots i)
      (TreeGraft.branchVertex_injective (A := family.Carrier) i) = (family.pointed i).first.toUnrooted := by
  apply TopologicalEmbedding.ext
  funext a
  rfl

theorem second_restrict (i : family.Index) :
    family.second.toUnrooted.precomposeHom (TreeGraft.includeHom family.trees family.roots i)
      (TreeGraft.branchVertex_injective (A := family.Carrier) i) = (family.pointed i).second.toUnrooted := by
  apply TopologicalEmbedding.ext
  funext a
  rfl

/-- Exact parent and branch score of the concrete assembled witness. -/
theorem score_eq (weights : Scoring V W) (penalty : WithTop ℝ) :
    score left right weights penalty family.pairs = weights.node u v + ∑ i : family.Index,
      (pathScore left right weights penalty s(u,(family.witness i.val).2.1) s(v,(family.witness i.val).2.2) +
        score left right weights penalty (family.witness i.val).1) := by
  rw [pairs, score_pairedImage, realizationScore_graft family.trees family.roots]
  simp only [RootedTopologicalEmbedding.toUnrooted_map]
  rw [family.first_root, family.second_root]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [family.first_branch_root, family.second_branch_root, family.first_restrict, family.second_restrict]
  exact congrArg (fun x : WithBot ℝ => pathScore left right weights penalty
    s(u,(family.witness i.val).2.1) s(v,(family.witness i.val).2.2) + x)
    ((family.pointed i).score_eq weights penalty)

/-- The assembled score expressed exactly in mapped/skipped boundary rewards. -/
theorem boundary_score_eq (weights : Scoring V W) (penalty : WithTop ℝ) :
    score left right weights penalty family.pairs = weights.node u v + ∑ i : family.Index,
      (if (family.witness i.val).2 = i.val then
        weights.edge s(u,i.val.1) s(v,i.val.2) +
          stateScore left right weights penalty i.val.1 i.val.2 (family.witness i.val).1 (family.witness i.val).2
       else stateScore left right weights penalty i.val.1 i.val.2 (family.witness i.val).1 (family.witness i.val).2) := by
  rw [family.score_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hv := family.valid i.val i.property
  exact connecting_reward_boundary weights penalty (family.witness i.val).1 (family.witness i.val).2
    (family.adjacent i.val i.property).1 (family.adjacent i.val i.property).2 hv.2.2.2.1 hv.2.2.2.2

end BoundaryFamily
end SubtreeProofs.Droschinsky2018

end
