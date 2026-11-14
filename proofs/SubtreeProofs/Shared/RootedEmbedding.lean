module

public import SubtreeProofs.Shared.TopologicalEmbedding
public import SubtreeProofs.Shared.RootedFork

/-!
# Rooted source embeddings and ancestry

These lemmas work from the two local clauses of 2018 Definition 1, rather
than assuming the global edge-path realization invariant.
-/

@[expose] public section

namespace SubtreeProofs.FiniteTree

variable {V : Type*} (tree : FiniteTree V)

/-- Along a simple ancestor-to-descendant path every step is a child step. -/
theorem ancestor_path_induction {root a b : V} (walk : tree.graph.Walk a b)
    (hw : walk.IsPath) (ha : tree.Ancestor root a b) (P : V → Prop) (hstart : P a)
    (hstep : ∀ u v, tree.Child root u v → P u → P v) : P b := by
  induction walk with
  | nil => exact hstart
  | @cons a c b hac rest ih =>
    have htail := (SimpleGraph.Walk.cons_isPath_iff hac rest).mp hw
    have hwalk := congrArg Subtype.val (tree.path_unique
      ⟨SimpleGraph.Walk.cons hac rest, hw⟩ (tree.path a b))
    have hc : c ∈ (tree.path a b).val.support := by
      rw [← hwalk]
      simp [rest.start_mem_support]
    have hac' := tree.ancestor_of_mem_suffix ha hc
    have hcb : tree.Ancestor root c b := by
      unfold Ancestor
      rw [← tree.path_append_of_ancestor ha]
      exact SimpleGraph.Walk.support_subset_support_append_right _ _ hc
    exact ih htail.1 hcb (hstep a c ⟨hac, hac'⟩ hstart)

end SubtreeProofs.FiniteTree

namespace SubtreeProofs.RootedTopologicalEmbedding

variable {A V : Type*} [DecidableEq V]
  {common : FiniteTree A} {target : FiniteTree V} {commonRoot : A} {targetRoot : V}

/-- The source's local descendant clause implies ancestry preservation for
all pairs of abstract vertices. -/
theorem ancestor_preserved (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    {a b : A} (ha : common.Ancestor commonRoot a b) :
    target.Ancestor targetRoot (embedding.map a) (embedding.map b) := by
  apply common.ancestor_path_induction (common.path a b).val (common.path a b).property ha
    (fun x => target.Ancestor targetRoot (embedding.map a) (embedding.map x))
    (target.ancestor_refl _ _)
  intro u v huv hprev
  exact target.ancestor_trans hprev (embedding.downward u v huv)

/-- Distinct abstract children enter distinct first target branches. -/
theorem firstChild_ne (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    {u c d : A} (hc : common.Child commonRoot u c) (hd : common.Child commonRoot u d) (hn : c ≠ d) :
    target.firstChild (embedding.map u) (embedding.map c) ≠
      target.firstChild (embedding.map u) (embedding.map d) := by
  intro he
  let x := target.firstChild (embedding.map u) (embedding.map c)
  have hx : x ∈ target.pathVertices (embedding.map u) (embedding.map c) :=
    List.mem_toFinset.mpr target.firstChild_ancestor
  have hy : x ∈ target.pathVertices (embedding.map u) (embedding.map d) := by
    change target.firstChild (embedding.map u) (embedding.map c) ∈ _
    rw [he]
    exact List.mem_toFinset.mpr target.firstChild_ancestor
  have hroot := (embedding.branches u c d hc hd hn x).mp ⟨hx, hy⟩
  have hne : embedding.map u ≠ embedding.map c := fun he => hc.1.ne (embedding.injective he)
  exact (target.firstChild_adj hne).ne hroot.symm

/-- The local source clauses reflect ancestry: incomparable branches cannot
collapse onto comparable target paths. -/
theorem ancestor_reflected (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    {a b : A} (ht : target.Ancestor targetRoot (embedding.map a) (embedding.map b)) :
    common.Ancestor commonRoot a b := by
  by_contra hn
  by_cases hba : common.Ancestor commonRoot b a
  · have he := embedding.injective (target.ancestor_antisymm ht (embedding.ancestor_preserved hba))
    exact hn (he ▸ common.ancestor_refl commonRoot a)
  · obtain ⟨u, c, d, hc, hd, hcd, hca, hdb⟩ := common.incomparable_fork hn hba
    have huc := embedding.downward u c hc
    have hud := embedding.downward u d hd
    have hcb := target.ancestor_trans (embedding.ancestor_preserved hca) ht
    have hdb' := embedding.ancestor_preserved hdb
    have hcpath := target.ancestor_interval huc hcb
    have hdpath := target.ancestor_interval hud hdb'
    have hucne : embedding.map u ≠ embedding.map c := fun he => hc.1.ne (embedding.injective he)
    have hudne : embedding.map u ≠ embedding.map d := fun he => hd.1.ne (embedding.injective he)
    have he := target.child_branches_disjoint (target.firstChild_adj hucne) (target.firstChild_adj hudne)
      (target.ancestor_trans target.firstChild_ancestor hcpath)
      (target.ancestor_trans target.firstChild_ancestor hdpath)
    exact embedding.firstChild_ne hc hd hcd he

/-- Exact rooted ancestry correspondence from the source's local definition. -/
theorem ancestor_iff (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot) (a b : A) :
    target.Ancestor targetRoot (embedding.map a) (embedding.map b) ↔ common.Ancestor commonRoot a b :=
  ⟨embedding.ancestor_reflected, embedding.ancestor_preserved⟩

/-- A mapped vertex can lie on a realized abstract edge only at an endpoint. -/
theorem mapped_vertex_on_edge (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    {a b c : A} (ha : common.graph.Adj a b) :
    embedding.map c ∈ target.pathVertices (embedding.map a) (embedding.map b) ↔ c = a ∨ c = b := by
  have hforward (u v : A) (huv : common.Child commonRoot u v)
      (hx : embedding.map c ∈ target.pathVertices (embedding.map u) (embedding.map v)) : c = u ∨ c = v := by
    have hdown := embedding.downward u v huv
    have hmem := List.mem_toFinset.mp hx
    have huc := target.ancestor_of_mem_suffix hdown hmem
    have hcv := target.suffix_ancestor hdown hmem
    exact (common.mem_path_of_adj huv.1).mp (common.ancestor_interval
      (embedding.ancestor_reflected huc) (embedding.ancestor_reflected hcv))
  constructor
  · intro hx
    rcases common.adjacent_ancestors commonRoot ha with hab | hba
    · exact hforward a b ⟨ha, hab⟩ hx
    · have hx' : embedding.map c ∈ target.pathVertices (embedding.map b) (embedding.map a) := by
        rw [target.pathVertices_comm]; exact hx
      exact (hforward b a ⟨ha.symm, hba⟩ hx').symm
  · rintro (rfl | rfl)
    · exact List.mem_toFinset.mpr (target.path _ _).val.start_mem_support
    · exact List.mem_toFinset.mpr (target.path _ _).val.end_mem_support

/-- Local rooted source conditions imply global avoidance of all mapped vertices. -/
theorem avoids_vertices (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    (a b : A) (ha : common.graph.Adj a b) (c : A) :
    embedding.map c ∉ target.pathInterior (embedding.map a) (embedding.map b) := by
  intro hc
  have hca := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcb := Finset.ne_of_mem_erase hc
  have hm := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  rcases (embedding.mapped_vertex_on_edge ha).mp hm with rfl | rfl
  · exact hca rfl
  · exact hcb rfl

/-- Interior disjointness first for edges oriented away from the common root. -/
theorem child_interiors_disjoint (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot)
    {a b c d : A} (hab : common.Child commonRoot a b) (hcd : common.Child commonRoot c d)
    (hn : s(a,b) ≠ s(c,d)) :
    Disjoint (target.pathInterior (embedding.map a) (embedding.map b))
      (target.pathInterior (embedding.map c) (embedding.map d)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxmem := List.mem_toFinset.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
  have hymem := List.mem_toFinset.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
  have hab' := embedding.downward a b hab
  have hcd' := embedding.downward c d hcd
  have hax := target.ancestor_of_mem_suffix hab' hxmem
  have hxb := target.suffix_ancestor hab' hxmem
  have hcx := target.ancestor_of_mem_suffix hcd' hymem
  have hxd := target.suffix_ancestor hcd' hymem
  have he : a = c := by
    rcases target.ancestors_comparable hax hcx with hac | hca
    · have hcpath := target.ancestor_interval hac (target.ancestor_trans hcx hxb)
      rcases (embedding.mapped_vertex_on_edge hab.1).mp (List.mem_toFinset.mpr hcpath) with he | he
      · exact he.symm
      · subst c
        have hxe := target.ancestor_antisymm hxb hcx
        exact False.elim (Finset.ne_of_mem_erase hx hxe)
    · have hapath := target.ancestor_interval hca (target.ancestor_trans hax hxd)
      rcases (embedding.mapped_vertex_on_edge hcd.1).mp (List.mem_toFinset.mpr hapath) with he | he
      · exact he
      · subst a
        have hxe := target.ancestor_antisymm hxd hax
        exact False.elim (Finset.ne_of_mem_erase hy hxe)
  subst c
  have hbd : b ≠ d := by intro he; exact hn (he ▸ rfl)
  have hxroot := (embedding.branches a b d hab hcd hbd x).mp
    ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx),
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)⟩
  exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx) hxroot

/-- Both local clauses of 2018 Definition 1 imply the independent global
path-realization invariant, without assuming a root-to-root restriction. -/
def toUnrooted (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot) :
    TopologicalEmbedding common target where
  map := embedding.map
  injective := embedding.injective
  avoids_vertices := embedding.avoids_vertices
  interior_disjoint := by
    intro a b hab c d hcd hn
    rcases common.adjacent_ancestors commonRoot hab with hab' | hba'
    · rcases common.adjacent_ancestors commonRoot hcd with hcd' | hdc'
      · exact embedding.child_interiors_disjoint ⟨hab, hab'⟩ ⟨hcd, hcd'⟩ hn
      · rw [target.pathInterior_comm (embedding.map c) (embedding.map d)]
        apply embedding.child_interiors_disjoint ⟨hab, hab'⟩ ⟨hcd.symm, hdc'⟩
        intro he
        exact hn (he.trans Sym2.eq_swap)
    · rw [target.pathInterior_comm (embedding.map a) (embedding.map b)]
      rcases common.adjacent_ancestors commonRoot hcd with hcd' | hdc'
      · apply embedding.child_interiors_disjoint ⟨hab.symm, hba'⟩ ⟨hcd, hcd'⟩
        intro he
        exact hn (Sym2.eq_swap.trans he)
      · rw [target.pathInterior_comm (embedding.map c) (embedding.map d)]
        apply embedding.child_interiors_disjoint ⟨hab.symm, hba'⟩ ⟨hcd.symm, hdc'⟩
        intro he
        exact hn (Sym2.eq_swap.trans (he.trans Sym2.eq_swap))

end SubtreeProofs.RootedTopologicalEmbedding

end
