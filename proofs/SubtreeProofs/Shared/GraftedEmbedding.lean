module

public import SubtreeProofs.Shared.TreeGraft
public import SubtreeProofs.Shared.RootedEmbedding

/-!
# Gluing rooted realizations in distinct input-child branches

An injective assignment of branch trees to distinct child regions lets their
source-style embeddings share one fresh mapped root. Both local clauses of
the rooted embedding definition are proved for the assembled map.
-/

@[expose] public section

namespace SubtreeProofs.GraftedEmbedding

variable {I : Type*} {A : I → Type*} {V : Type*}
  [Fintype I] [∀ i, Fintype (A i)] [DecidableEq V]

variable {trees : ∀ i, FiniteTree (A i)} {roots : ∀ i, A i}
  {target : FiniteTree V} {base : V} (parent : V)
  (embeddings : ∀ i, RootedTopologicalEmbedding (trees i) target (roots i) base)
  (children : I → V)
  (hchildren : Function.Injective children)
  (hadj : ∀ i, target.Child base parent (children i))
  (hregion : ∀ i a, target.Ancestor base (children i) ((embeddings i).map a))

/-- The new root maps to the parent; each branch retains its supplied map. -/
def map : TreeGraft.Vertex A → V
  | none => parent
  | some ⟨i,a⟩ => (embeddings i).map a

omit [Fintype I] [∀ i, Fintype (A i)] in
include hchildren hadj hregion in
/-- Different source branches cannot share a target vertex. -/
theorem branch_index {i j : I} (a : A i) (b : A j)
    (he : (embeddings i).map a = (embeddings j).map b) : i = j := by
  have hi := target.ancestor_interval (hadj i).2 (hregion i a)
  have hj := target.ancestor_interval (hadj j).2 (hregion j b)
  rw [he] at hi
  exact hchildren (target.child_branches_disjoint (hadj i).1 (hadj j).1 hi hj)

omit [Fintype I] [∀ i, Fintype (A i)] in
include hchildren hadj hregion in
theorem map_injective : Function.Injective (map parent embeddings) := by
  intro first second he
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some second =>
      rcases second with ⟨j,b⟩
      exact False.elim (target.child_descendant_ne_parent (hadj j) (hregion j b) he.symm)
  | some first =>
    rcases first with ⟨i,a⟩
    cases second with
    | none => exact False.elim (target.child_descendant_ne_parent (hadj i) (hregion i a) he)
    | some second =>
      rcases second with ⟨j,b⟩
      have hij := branch_index parent embeddings children hchildren hadj hregion a b he
      subst j
      exact congrArg (TreeGraft.branchVertex i) ((embeddings i).injective he)

/-- Rooted source embedding of the grafted common tree, with no assumptions
about its validity beyond the independent branch and child-region data. -/
def embedding : RootedTopologicalEmbedding (TreeGraft.tree trees roots) target none base where
  map := map parent embeddings
  injective := map_injective parent embeddings children hchildren hadj hregion
  downward := by
    intro p q hpq
    rcases TreeGraft.child_cases trees roots p q hpq with ⟨i, rfl, rfl⟩ | ⟨i, a, b, rfl, rfl, hab⟩
    · exact target.ancestor_trans (hadj i).2 (hregion i (roots i))
    · exact (embeddings i).downward a b hab
  branches := by
    intro p q r hpq hpr hqr x
    cases p with
    | none =>
      obtain ⟨i, rfl⟩ := TreeGraft.child_from_root trees roots q hpq
      obtain ⟨j, rfl⟩ := TreeGraft.child_from_root trees roots r hpr
      have hij : i ≠ j := by intro he; subst j; exact hqr rfl
      exact target.child_paths_intersection (hadj i) (hadj j)
        (fun he => hij (hchildren he)) (hregion i (roots i)) (hregion j (roots j)) x
    | some p =>
      rcases p with ⟨i,a⟩
      obtain ⟨b, rfl, hab⟩ := TreeGraft.child_from_branch trees roots i a q hpq
      obtain ⟨c, rfl, hac⟩ := TreeGraft.child_from_branch trees roots i a r hpr
      have hbc : b ≠ c := by intro he; exact hqr (congrArg (TreeGraft.branchVertex i) he)
      exact (embeddings i).branches a b c hab hac hbc x

@[simp] theorem embedding_root :
    (embedding parent embeddings children hchildren hadj hregion).map none = parent := rfl

end SubtreeProofs.GraftedEmbedding

end
