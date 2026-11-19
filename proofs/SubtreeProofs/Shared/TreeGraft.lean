module

public import SubtreeProofs.Shared.RootedTree
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Grafting finitely many trees beneath a fresh root

The carrier keeps every branch vertex distinct. The tree invariant is derived
from connectivity and the exact edge/vertex count, using Mathlib's finite-tree
criterion. This is the common-tree constructor needed for embedding assembly.
-/

@[expose] public section

namespace SubtreeProofs.TreeGraft

variable {I : Type*} {A : I → Type*} [Fintype I] [∀ i, Fintype (A i)]

abbrev Vertex (A : I → Type*) := Option (Sigma A)

def branchVertex (i : I) (a : A i) : Vertex A := some ⟨i,a⟩

omit [Fintype I] [∀ i, Fintype (A i)] in
theorem branchVertex_injective (i : I) : Function.Injective (branchVertex (A := A) i) :=
  fun _ _ he => sigma_mk_injective (Option.some.inj he)

noncomputable def branchEdges (trees : ∀ i, FiniteTree (A i)) (i : I) : Finset (Sym2 (Vertex A)) := by
  classical
  exact (trees i).graph.edgeFinset.image (Sym2.map (branchVertex i))

noncomputable def connectors (roots : ∀ i, A i) : Finset (Sym2 (Vertex A)) := by
  classical
  exact Finset.univ.image (fun i => s(none, branchVertex i (roots i)))

noncomputable def branches (trees : ∀ i, FiniteTree (A i)) : Finset (Sym2 (Vertex A)) := by
  classical
  exact Finset.univ.biUnion (branchEdges trees)

noncomputable def edges (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) : Finset (Sym2 (Vertex A)) := by
  classical
  exact connectors roots ∪ branches trees

noncomputable def graph (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) : SimpleGraph (Vertex A) :=
  SimpleGraph.fromEdgeSet (↑(edges trees roots) : Set (Sym2 (Vertex A)))

omit [Fintype I] [∀ i, Fintype (A i)] in
theorem connector_injective (roots : ∀ i, A i) :
    Function.Injective (fun i => s(none, branchVertex i (roots i))) := by
  intro i j he
  have hv := (Sym2.mkEmbedding none).injective he
  exact congrArg Sigma.fst (Option.some.inj hv)

omit [Fintype I] in
theorem none_notMem_branch (trees : ∀ i, FiniteTree (A i)) (i : I)
    {edge : Sym2 (Vertex A)} (he : edge ∈ branchEdges trees i) : none ∉ edge := by
  classical
  obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp he
  intro hn
  obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hn
  cases ha

omit [Fintype I] in
theorem branchEdges_disjoint (trees : ∀ i, FiniteTree (A i)) {i j : I} (hn : i ≠ j) :
    Disjoint (branchEdges trees i) (branchEdges trees j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro edge hi hj
  obtain ⟨first, _, he⟩ := Finset.mem_image.mp hi
  obtain ⟨second, _, hs⟩ := Finset.mem_image.mp hj
  have hx : branchVertex i first.out.1 ∈ Sym2.map (branchVertex j) second := by
    rw [hs, ← he]
    exact Sym2.mem_map.mpr ⟨first.out.1, first.out_fst_mem, rfl⟩
  obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hx
  exact hn (congrArg Sigma.fst (Option.some.inj ha)).symm

theorem connectors_disjoint (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) :
    Disjoint (connectors roots) (branches trees) := by
  classical
  apply Finset.disjoint_left.mpr
  intro edge he hb
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hb
  exact none_notMem_branch trees j hj (Sym2.mem_mk_left _ _)

theorem edges_not_isDiag (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    {edge : Sym2 (Vertex A)} (he : edge ∈ edges trees roots) : ¬ edge.IsDiag := by
  classical
  rcases Finset.mem_union.mp he with hc | hb
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    simp [Sym2.mk_isDiag_iff, branchVertex]
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨original, ho, rfl⟩ := Finset.mem_image.mp hi
    intro hd
    exact (trees i).graph.not_isDiag_of_mem_edgeFinset ho
      ((Sym2.isDiag_map (branchVertex_injective i)).mp hd)

theorem edgeSet_eq (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) :
    (graph trees roots).edgeSet = (↑(edges trees roots) : Set (Sym2 (Vertex A))) := by
  rw [graph, SimpleGraph.edgeSet_fromEdgeSet]
  ext edge
  change (edge ∈ edges trees roots ∧ ¬ edge.IsDiag) ↔ edge ∈ edges trees roots
  exact ⟨And.left, fun he => ⟨he, edges_not_isDiag trees roots he⟩⟩

/-- Branch edges preserve the original branch adjacency. -/
def includeHom (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) (i : I) :
    (trees i).graph →g graph trees roots where
  toFun := branchVertex i
  map_rel' := by
    classical
    intro a b hab
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩), ?_⟩
    · exact Finset.mem_image.mpr ⟨s(a,b),
        (SimpleGraph.mem_edgeFinset).mpr ((SimpleGraph.mem_edgeSet (trees i).graph).mpr hab), rfl⟩
    · exact fun he => hab.ne (branchVertex_injective i he)

theorem root_adj (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) (i : I) :
    (graph trees roots).Adj none (branchVertex i (roots i)) := by
  classical
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), by simp [branchVertex]⟩

/-- The fresh root reaches every branch vertex through that branch's root. -/
theorem connected (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) : (graph trees roots).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, ?_⟩
  intro vertex
  cases vertex with
  | none => exact SimpleGraph.Reachable.refl _
  | some vertex =>
    rcases vertex with ⟨i,a⟩
    exact (root_adj trees roots i).reachable.trans
      (((trees i).isTree.connected (roots i) a).map (includeHom trees roots i))

/-- The exact edge count of a graft is the sum of its branch vertex counts. -/
theorem edges_card (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) :
    (edges trees roots).card = ∑ i, Fintype.card (A i) := by
  classical
  rw [edges, Finset.card_union_of_disjoint (connectors_disjoint trees roots), branches,
    Finset.card_biUnion (fun i _ j _ hn => branchEdges_disjoint trees hn)]
  have hc : (connectors roots).card = Fintype.card I := by
    rw [connectors, Finset.card_image_of_injective _ (connector_injective roots)]
    rfl
  rw [hc]
  have hb (i : I) : (branchEdges trees i).card = (trees i).graph.edgeFinset.card := by
    rw [branchEdges, Finset.card_image_of_injective _ (Sym2.map.injective (branchVertex_injective i))]
  simp_rw [hb]
  have hs : (∑ i, (trees i).graph.edgeFinset.card) + Fintype.card I = ∑ i, Fintype.card (A i) := by
    calc
      _ = ∑ i, ((trees i).graph.edgeFinset.card + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun i _ => (trees i).isTree.card_edgeFinset)
  omega

/-- Connectivity and the exact finite cardinality establish the grafted tree invariant. -/
theorem isTree (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) : (graph trees roots).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected trees roots, ?_⟩
  rw [edgeSet_eq]
  simp only [Nat.card_eq_fintype_card, Finset.coe_sort_coe, Fintype.card_coe, Fintype.card_option, Fintype.card_sigma]
  change (edges trees roots).card + 1 = (∑ i, Fintype.card (A i)) + 1
  rw [edges_card]

noncomputable def tree (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) : FiniteTree (Vertex A) :=
  ⟨graph trees roots, isTree trees roots⟩

/-- Root paths enter a branch once and follow its own canonical root path. -/
theorem root_path (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) (i : I) (a : A i) :
    ((tree trees roots).path none (branchVertex i a)).val =
      SimpleGraph.Walk.cons (root_adj trees roots i)
        (((trees i).path (roots i) a).val.map (includeHom trees roots i)) := by
  let q := ((trees i).path (roots i) a).val.map (includeHom trees roots i)
  have hq : q.IsPath := ((trees i).path (roots i) a).property.map (branchVertex_injective i)
  have hn : none ∉ q.support := by
    rw [SimpleGraph.Walk.support_map]
    intro hm
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hm
    cases hb
  have hp := (SimpleGraph.Walk.cons_isPath_iff (root_adj trees roots i) q).mpr ⟨hq, hn⟩
  exact congrArg Subtype.val ((tree trees roots).path_unique _ ⟨_, hp⟩)

/-- Root adjacency picks exactly the given root of each branch. -/
theorem root_adj_iff (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i) (i : I) (a : A i) :
    (graph trees roots).Adj none (branchVertex i a) ↔ a = roots i := by
  classical
  constructor
  · intro ha
    have he := (SimpleGraph.fromEdgeSet_adj _).mp ha
    rcases Finset.mem_union.mp he.1 with hc | hb
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      have hv := (Sym2.mkEmbedding none).injective hj
      have hij : j = i := congrArg Sigma.fst (Option.some.inj hv)
      subst j
      exact (branchVertex_injective i hv).symm
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hb
      exact False.elim (none_notMem_branch trees j hj (Sym2.mem_mk_left _ _))
  · rintro rfl
    exact root_adj trees roots i

/-- Non-root edges remain within one branch. -/
theorem branch_adj_index (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    {i j : I} (a : A i) (b : A j)
    (ha : (graph trees roots).Adj (branchVertex i a) (branchVertex j b)) : i = j := by
  classical
  have he := (SimpleGraph.fromEdgeSet_adj _).mp ha
  rcases Finset.mem_union.mp he.1 with hc | hb
  · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hc
    have hn : none ∈ s(branchVertex i a, branchVertex j b) := hk ▸ Sym2.mem_mk_left _ _
    simp [branchVertex] at hn
  · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨original, _, ho⟩ := Finset.mem_image.mp hk
    have hleft : branchVertex i a ∈ Sym2.map (branchVertex k) original := ho ▸ Sym2.mem_mk_left _ _
    have hright : branchVertex j b ∈ Sym2.map (branchVertex k) original := ho ▸ Sym2.mem_mk_right _ _
    obtain ⟨x, _, hx⟩ := Sym2.mem_map.mp hleft
    obtain ⟨y, _, hy⟩ := Sym2.mem_map.mp hright
    have hki := congrArg Sigma.fst (Option.some.inj hx)
    have hkj := congrArg Sigma.fst (Option.some.inj hy)
    exact hki.symm.trans hkj

theorem branch_adj_iff (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    (i : I) (a b : A i) :
    (graph trees roots).Adj (branchVertex i a) (branchVertex i b) ↔ (trees i).graph.Adj a b := by
  classical
  constructor
  · intro ha
    have he := (SimpleGraph.fromEdgeSet_adj _).mp ha
    rcases Finset.mem_union.mp he.1 with hc | hb
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hc
      have hn : none ∈ s(branchVertex i a, branchVertex i b) := hk ▸ Sym2.mem_mk_left _ _
      simp [branchVertex] at hn
    · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hb
      obtain ⟨original, ho, heq⟩ := Finset.mem_image.mp hk
      have hleft : branchVertex i a ∈ Sym2.map (branchVertex k) original := heq ▸ Sym2.mem_mk_left _ _
      obtain ⟨x, _, hx⟩ := Sym2.mem_map.mp hleft
      have hki : k = i := congrArg Sigma.fst (Option.some.inj hx)
      subst k
      have heq' : Sym2.map (branchVertex i) original = Sym2.map (branchVertex i) s(a,b) := by
        simpa only [Sym2.map_mk] using heq
      have horiginal := Sym2.map.injective (branchVertex_injective i) heq'
      rw [horiginal] at ho
      exact (SimpleGraph.mem_edgeSet _).mp ((SimpleGraph.mem_edgeFinset).mp ho)
  · exact (includeHom trees roots i).map_rel

/-- The graft's rooted orientation restricts to each branch's own orientation. -/
theorem branch_ancestor_iff (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    (i : I) (a b : A i) :
    (tree trees roots).Ancestor none (branchVertex i a) (branchVertex i b) ↔
      (trees i).Ancestor (roots i) a b := by
  unfold FiniteTree.Ancestor
  rw [root_path]
  dsimp only [tree, includeHom]
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_map, List.mem_cons]
  constructor
  · rintro (hn | hm)
    · cases hn
    · obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
      exact branchVertex_injective i he ▸ hx
  · intro ha
    exact Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- Every oriented child edge is a new-root connector or an original oriented
edge of exactly one branch. -/
theorem child_cases (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    (p q : Vertex A) (h : (tree trees roots).Child none p q) :
    (∃ i, p = none ∧ q = branchVertex i (roots i)) ∨
      ∃ i a b, p = branchVertex i a ∧ q = branchVertex i b ∧ (trees i).Child (roots i) a b := by
  cases p with
  | none =>
    cases q with
    | none => exact False.elim (h.1.ne rfl)
    | some q =>
      rcases q with ⟨i,a⟩
      have he := (root_adj_iff trees roots i a).mp h.1
      exact Or.inl ⟨i, rfl, congrArg (branchVertex i) he⟩
  | some p =>
    rcases p with ⟨i,a⟩
    cases q with
    | none =>
      have he := (tree trees roots).ancestor_antisymm h.2 ((tree trees roots).root_ancestor _ _)
      cases he
    | some q =>
      rcases q with ⟨j,b⟩
      have hij := branch_adj_index trees roots a b h.1
      subst j
      exact Or.inr ⟨i, a, b, rfl, rfl,
        (branch_adj_iff trees roots i a b).mp h.1, (branch_ancestor_iff trees roots i a b).mp h.2⟩

theorem child_from_root (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    (q : Vertex A) (h : (tree trees roots).Child none none q) :
    ∃ i, q = branchVertex i (roots i) := by
  rcases child_cases trees roots none q h with ⟨i, _, hq⟩ | ⟨i, a, b, hp, _, _⟩
  · exact ⟨i,hq⟩
  · cases hp

theorem child_from_branch (trees : ∀ i, FiniteTree (A i)) (roots : ∀ i, A i)
    (i : I) (a : A i) (q : Vertex A) (h : (tree trees roots).Child none (branchVertex i a) q) :
    ∃ b, q = branchVertex i b ∧ (trees i).Child (roots i) a b := by
  rcases child_cases trees roots (branchVertex i a) q h with ⟨j, hp, _⟩ | ⟨j, c, d, hp, hq, hcd⟩
  · cases hp
  · have hij : i = j := congrArg Sigma.fst (Option.some.inj hp)
    subst j
    have he := branchVertex_injective i hp
    subst c
    exact ⟨d, hq, hcd⟩

end SubtreeProofs.TreeGraft

end
