module

public import SubtreeProofs.Shared.RootedTree
import Mathlib.Tactic

/-!
# Common ancestors and distinct rooted branches

Finite canonical paths suffice; the vertex type need not be finite. These
lemmas support the converse from local rooted embedding clauses to global
path realizations.
-/

@[expose] public section

namespace SubtreeProofs.FiniteTree

variable {V : Type*} (tree : FiniteTree V)

/-- Ancestors of a single vertex are linearly ordered along its root path. -/
theorem ancestors_comparable {root a b vertex : V}
    (ha : tree.Ancestor root a vertex) (hb : tree.Ancestor root b vertex) :
    tree.Ancestor root a b ∨ tree.Ancestor root b a := by
  unfold Ancestor at ha
  rw [← tree.path_append_of_ancestor hb] at ha
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp ha with hp | hq
  · exact Or.inl hp
  · exact Or.inr (tree.ancestor_of_mem_suffix hb hq)

/-- The interval between comparable vertices is the canonical suffix path. -/
theorem ancestor_interval {root a b c : V}
    (hac : tree.Ancestor root a c) (hcb : tree.Ancestor root c b) :
    c ∈ (tree.path a b).val.support := by
  have hab := tree.ancestor_trans hac hcb
  unfold Ancestor at hcb
  rw [← tree.path_append_of_ancestor hab] at hcb
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hcb with hca | hpath
  · have he := tree.ancestor_antisymm hca hac
    exact he ▸ (tree.path a b).val.start_mem_support
  · exact hpath

/-- Points on an ancestor suffix are ancestors of the suffix's endpoint. -/
theorem suffix_ancestor {root a b c : V} (hab : tree.Ancestor root a b)
    (hc : c ∈ (tree.path a b).val.support) : tree.Ancestor root c b := by
  unfold Ancestor
  rw [← tree.path_append_of_ancestor hab]
  exact SimpleGraph.Walk.support_subset_support_append_right _ _ hc

/-- A canonical path across one actual edge has just its two endpoints. -/
theorem mem_path_of_adj {a b c : V} (ha : tree.graph.Adj a b) :
    c ∈ (tree.path a b).val.support ↔ c = a ∨ c = b := by
  have he := congrArg Subtype.val (tree.path_unique (tree.path a b) (SimpleGraph.Path.singleton ha))
  rw [he]
  simp [SimpleGraph.Path.singleton]

@[simp] theorem pathLength_self (a : V) : tree.pathLength a a = 0 := by
  have he := congrArg Subtype.val (tree.path_unique (tree.path a a) SimpleGraph.Path.nil)
  unfold pathLength
  rw [he]
  rfl

theorem pathLength_adj {a b : V} (ha : tree.graph.Adj a b) : tree.pathLength a b = 1 := by
  have he := congrArg Subtype.val (tree.path_unique (tree.path a b) (SimpleGraph.Path.singleton ha))
  unfold pathLength
  rw [he]
  rfl

/-- Descending one child on the way to a descendant removes exactly one edge. -/
theorem pathLength_child_step {root u c v : V} (hc : tree.Child root u c)
    (hv : tree.Ancestor root c v) : tree.pathLength u v = tree.pathLength c v + 1 := by
  have hlocal : tree.Ancestor u c v := tree.ancestor_interval hc.2 hv
  have he := congrArg SimpleGraph.Walk.length (tree.path_append_of_ancestor hlocal)
  rw [SimpleGraph.Walk.length_append] at he
  change tree.pathLength u c + tree.pathLength c v = tree.pathLength u v at he
  rw [tree.pathLength_adj hc.1] at he
  omega

/-- A path starting at a parent stays in its chosen child branch after leaving
that parent. -/
theorem path_in_child_branch [DecidableEq V] {root u c v x : V} (hc : tree.Child root u c)
    (hv : tree.Ancestor root c v) (hx : x ∈ tree.pathVertices u v) :
    x = u ∨ tree.Ancestor u c x := by
  have hlocal : tree.Ancestor u c v := tree.ancestor_interval hc.2 hv
  have hm := List.mem_toFinset.mp hx
  rw [← tree.path_append_of_ancestor hlocal] at hm
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hm with hfirst | htail
  · rcases (tree.mem_path_of_adj hc.1).mp hfirst with he | he
    · exact Or.inl he
    · exact Or.inr (he ▸ tree.ancestor_refl u c)
  · exact Or.inr (tree.ancestor_of_mem_suffix hlocal htail)

/-- Different child branches give paths whose only common vertex is the parent. -/
theorem child_paths_intersection [DecidableEq V] {root u c d v w : V}
    (hc : tree.Child root u c) (hd : tree.Child root u d) (hn : c ≠ d)
    (hv : tree.Ancestor root c v) (hw : tree.Ancestor root d w) (x : V) :
    (x ∈ tree.pathVertices u v ∧ x ∈ tree.pathVertices u w) ↔ x = u := by
  constructor
  · rintro ⟨hx, hy⟩
    rcases tree.path_in_child_branch hc hv hx with he | hcx
    · exact he
    rcases tree.path_in_child_branch hd hw hy with he | hdx
    · exact he
    · exact False.elim (hn (tree.child_branches_disjoint hc.1 hd.1 hcx hdx))
  · intro he
    subst x
    exact ⟨List.mem_toFinset.mpr (tree.path u v).val.start_mem_support,
      List.mem_toFinset.mpr (tree.path u w).val.start_mem_support⟩

/-- No descendant of a child is its parent. -/
theorem child_descendant_ne_parent {root u c x : V} (hc : tree.Child root u c)
    (hx : tree.Ancestor root c x) : x ≠ u := by
  intro he
  subst x
  exact hc.1.ne (tree.ancestor_antisymm hc.2 hx)

/-- Every two vertices have a greatest common ancestor, proved from their
finite paths rather than assumed as a rooted-tree operation. -/
theorem exists_greatest_common_ancestor (root a b : V) :
    ∃ u, tree.Ancestor root u a ∧ tree.Ancestor root u b ∧
      ∀ v, tree.Ancestor root v a → tree.Ancestor root v b → tree.Ancestor root v u := by
  classical
  let shared := tree.pathVertices root a ∩ tree.pathVertices root b
  have hs : shared.Nonempty := ⟨root, Finset.mem_inter.mpr
    ⟨List.mem_toFinset.mpr (tree.path root a).val.start_mem_support,
      List.mem_toFinset.mpr (tree.path root b).val.start_mem_support⟩⟩
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image shared (tree.pathLength root) hs
  have hua : tree.Ancestor root u a := List.mem_toFinset.mp (Finset.mem_inter.mp hu).1
  have hub : tree.Ancestor root u b := List.mem_toFinset.mp (Finset.mem_inter.mp hu).2
  refine ⟨u, hua, hub, ?_⟩
  intro v hva hvb
  rcases tree.ancestors_comparable hva hua with h | h
  · exact h
  · by_cases he : v = u
    · subst v; exact tree.ancestor_refl _ _
    · have hlt := tree.ancestor_length_lt h (fun heq => he heq.symm)
      have hle := hmax v (Finset.mem_inter.mpr
        ⟨List.mem_toFinset.mpr hva, List.mem_toFinset.mpr hvb⟩)
      omega

/-- Incomparable vertices lie below different children of a common ancestor. -/
theorem incomparable_fork {root a b : V}
    (hab : ¬ tree.Ancestor root a b) (hba : ¬ tree.Ancestor root b a) :
    ∃ u c d, tree.Child root u c ∧ tree.Child root u d ∧ c ≠ d ∧
      tree.Ancestor root c a ∧ tree.Ancestor root d b := by
  obtain ⟨u, hua, hub, hgreatest⟩ := tree.exists_greatest_common_ancestor root a b
  have hua' : u ≠ a := by intro he; exact hab (he ▸ hub)
  have hub' : u ≠ b := by intro he; exact hba (he ▸ hua)
  let c := tree.firstChild u a
  let d := tree.firstChild u b
  have hc : tree.Child root u c := ⟨tree.firstChild_adj hua',
    tree.ancestor_of_mem_suffix hua tree.firstChild_ancestor⟩
  have hd : tree.Child root u d := ⟨tree.firstChild_adj hub',
    tree.ancestor_of_mem_suffix hub tree.firstChild_ancestor⟩
  have hca : tree.Ancestor root c a := tree.suffix_ancestor hua tree.firstChild_ancestor
  have hdb : tree.Ancestor root d b := tree.suffix_ancestor hub tree.firstChild_ancestor
  refine ⟨u, c, d, hc, hd, ?_, hca, hdb⟩
  intro he
  have hcu := hgreatest c hca (he ▸ hdb)
  exact hc.1.ne (tree.ancestor_antisymm hc.2 hcu)

end SubtreeProofs.FiniteTree

end
