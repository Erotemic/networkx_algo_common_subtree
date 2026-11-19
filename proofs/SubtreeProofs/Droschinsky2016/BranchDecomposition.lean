module

public import SubtreeProofs.Droschinsky2016.Rooted

/-!
# Structural branch decomposition of connected isomorphism witnesses

The branch partition uses canonical graph paths. It does not assume any
recursive optimum equations or Rust parent-array invariants.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The selected left vertex represented by a concrete mapped pair. -/
def atLeft (pairs : Mapping V W) (p : V × W) (hp : p ∈ pairs) : LeftVertices pairs :=
  ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

def atRight (pairs : Mapping V W) (p : V × W) (hp : p ∈ pairs) : RightVertices pairs :=
  ⟨p.2, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

theorem witnessMap_at {pairs : Mapping V W} (h : PartialBijection pairs)
    (p : V × W) (hp : p ∈ pairs) :
    witnessMap pairs (atLeft pairs p hp) = atRight pairs p hp := by
  apply Subtype.ext
  change (pairAtLeft pairs (atLeft pairs p hp)).2 = p.2
  have he := h.1 _ (pairAtLeft_mem pairs (atLeft pairs p hp)) p hp
    (pairAtLeft_fst pairs (atLeft pairs p hp))
  exact congrArg Prod.snd he

/-- Rooted ancestry in the selected subtree is preserved by every independent
connected induced-graph isomorphism witness. -/
theorem Valid.ancestor_preserved {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs)
    (root p q : V × W) (hr : root ∈ pairs) (hp : p ∈ pairs) (hq : q ∈ pairs) :
    left.Ancestor root.1 p.1 q.1 ↔ right.Ancestor root.2 p.2 q.2 := by
  let ls : FiniteTree (LeftVertices pairs) := ⟨_, h.left_isTree⟩
  let rs : FiniteTree (RightVertices pairs) := ⟨_, h.right_isTree⟩
  let li : ls.graph →g left.graph := ⟨Subtype.val, fun ha => ha⟩
  let ri : rs.graph →g right.graph := ⟨Subtype.val, fun ha => ha⟩
  let iso := h.inducedIso
  have hl := ls.ancestor_map_iff left li Subtype.val_injective
    (atLeft pairs root hr) (atLeft pairs p hp) (atLeft pairs q hq)
  have hm := ls.ancestor_map_iff rs iso.toHom iso.injective
    (atLeft pairs root hr) (atLeft pairs p hp) (atLeft pairs q hq)
  have hrr := rs.ancestor_map_iff right ri Subtype.val_injective
    (atRight pairs root hr) (atRight pairs p hp) (atRight pairs q hq)
  have he (entry : V × W) (he : entry ∈ pairs) :
      iso.toHom (atLeft pairs entry he) = atRight pairs entry he := witnessMap_at h.2.1 entry he
  rw [he root hr, he p hp, he q hq] at hm
  exact hl.trans (hm.symm.trans hrr.symm)

/-- Restriction to the left descendant region of one selected vertex. -/
noncomputable def branchMapping (left : FiniteTree V) (root child : V)
    (pairs : Mapping V W) : Mapping V W := by
  classical
  exact pairs.filter (fun p => left.Ancestor root child p.1)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem mem_branchMapping (left : FiniteTree V) (root child : V)
    (pairs : Mapping V W) (p : V × W) :
    p ∈ branchMapping left root child pairs ↔ p ∈ pairs ∧ left.Ancestor root child p.1 := by
  classical
  simp [branchMapping]

omit [DecidableEq W] in
theorem branchMapping_left_vertices (left : FiniteTree V) (root child : V)
    (pairs : Mapping V W) :
    (↑((branchMapping left root child pairs).image Prod.fst) : Set V) =
      {x | x ∈ pairs.image Prod.fst ∧ left.Ancestor root child x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have h := (mem_branchMapping left root child pairs p).mp hp
    exact ⟨Finset.mem_image.mpr ⟨p, h.1, rfl⟩, h.2⟩
  · rintro ⟨hx, ha⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨p, (mem_branchMapping left root child pairs p).mpr ⟨hp, ha⟩, rfl⟩

theorem Valid.branchMapping_right_vertices {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root child : V × W)
    (hr : root ∈ pairs) (hc : child ∈ pairs) :
    (↑((branchMapping left root.1 child.1 pairs).image Prod.snd) : Set W) =
      {x | x ∈ pairs.image Prod.snd ∧ right.Ancestor root.2 child.2 x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hm := (mem_branchMapping left root.1 child.1 pairs p).mp hp
    exact ⟨Finset.mem_image.mpr ⟨p, hm.1, rfl⟩,
      (h.ancestor_preserved root child p hr hc hm.1).mp hm.2⟩
  · rintro ⟨hx, ha⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨p,
      (mem_branchMapping left root.1 child.1 pairs p).mpr
        ⟨hp, (h.ancestor_preserved root child p hr hc hp).mpr ha⟩, rfl⟩

/-- Restricting a valid witness to a mapped descendant region yields another
nonempty connected isomorphism witness, with the same concrete pair mapping. -/
theorem Valid.branchMapping_valid {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root child : V × W)
    (hr : root ∈ pairs) (hc : child ∈ pairs) :
    Valid left right (branchMapping left root.1 child.1 pairs) := by
  have hsub : branchMapping left root.1 child.1 pairs ⊆ pairs := by
    intro p hp
    exact ((mem_branchMapping left root.1 child.1 pairs p).mp hp).1
  refine ⟨⟨child, (mem_branchMapping left root.1 child.1 pairs child).mpr
    ⟨hc, left.ancestor_refl _ _⟩⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun p hp q hq he => h.2.1.1 p (hsub hp) q (hsub hq) he,
      fun p hp q hq he => h.2.1.2 p (hsub hp) q (hsub hq) he⟩
  · rw [branchMapping_left_vertices]
    exact left.connected_descendant_inter h.2.2.1 root.1
      (Finset.mem_image.mpr ⟨child, hc, rfl⟩)
  · rw [h.branchMapping_right_vertices root child hr hc]
    exact right.connected_descendant_inter h.2.2.2.1 root.2
      (Finset.mem_image.mpr ⟨child, hc, rfl⟩)
  · intro p hp q hq
    exact h.2.2.2.2 p (hsub hp) q (hsub hq)

/-- Selected children of the chosen mapped root form a partial bijection. -/
noncomputable def childMapping (left : FiniteTree V) (root : V) (pairs : Mapping V W) : Mapping V W := by
  classical
  exact pairs.filter (fun p => left.graph.Adj root p.1)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem mem_childMapping (left : FiniteTree V) (root : V) (pairs : Mapping V W) (p : V × W) :
    p ∈ childMapping left root pairs ↔ p ∈ pairs ∧ left.graph.Adj root p.1 := by
  classical
  simp [childMapping]

/-- Each non-root mapped vertex belongs to exactly one selected child branch.
Existence uses connectedness; uniqueness uses acyclicity and partial injectivity. -/
theorem Valid.unique_child_branch {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root p : V × W)
    (hr : root ∈ pairs) (hp : p ∈ pairs) (hn : p ≠ root) :
    ∃! child, child ∈ childMapping left root.1 pairs ∧
      p ∈ branchMapping left root.1 child.1 pairs := by
  have hne : root.1 ≠ p.1 := by
    intro he
    exact hn (h.2.1.1 p hp root hr he.symm)
  let c := left.firstChild root.1 p.1
  have hc : c ∈ pairs.image Prod.fst := left.connected_path_closed h.2.2.1
    (Finset.mem_image.mpr ⟨root, hr, rfl⟩) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    c left.firstChild_ancestor
  obtain ⟨child, hchild, he⟩ := Finset.mem_image.mp hc
  have hadj : left.graph.Adj root.1 child.1 := he ▸ left.firstChild_adj hne
  have hbranch : left.Ancestor root.1 child.1 p.1 := he ▸ left.firstChild_ancestor
  refine ⟨child, ⟨(mem_childMapping left root.1 pairs child).mpr ⟨hchild, hadj⟩,
    (mem_branchMapping left root.1 child.1 pairs p).mpr ⟨hp, hbranch⟩⟩, ?_⟩
  intro other ho
  have hom := (mem_childMapping left root.1 pairs other).mp ho.1
  have hob := (mem_branchMapping left root.1 other.1 pairs p).mp ho.2
  exact h.2.1.1 other hom.1 child hchild
    (left.child_branches_disjoint hom.2 hadj hob.2 hbranch)

/-- Every branch in the structural partition is itself a root-to-root witness. -/
theorem Valid.child_branch_rooted {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root child : V × W)
    (hr : root ∈ pairs) (hc : child ∈ childMapping left root.1 pairs) :
    RootedValid left right root.1 root.2 child.1 child.2
      (branchMapping left root.1 child.1 pairs) := by
  have hchild := ((mem_childMapping left root.1 pairs child).mp hc).1
  refine ⟨h.branchMapping_valid root child hr hchild,
    (mem_branchMapping left root.1 child.1 pairs child).mpr ⟨hchild, left.ancestor_refl _ _⟩, ?_⟩
  intro p hp
  have hm := (mem_branchMapping left root.1 child.1 pairs p).mp hp
  exact ⟨hm.2, (h.ancestor_preserved root child p hr hchild hm.1).mp hm.2⟩

theorem Valid.root_notMem_child_branch {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (_h : Valid left right pairs) (root child : V × W)
    (hc : child ∈ childMapping left root.1 pairs) :
    root ∉ branchMapping left root.1 child.1 pairs := by
  intro hr
  have ha := ((mem_childMapping left root.1 pairs child).mp hc).2
  have hb := ((mem_branchMapping left root.1 child.1 pairs root).mp hr).2
  have he := left.ancestor_antisymm hb (left.root_ancestor root.1 child.1)
  exact ha.ne he.symm

/-- The child branches partition all selected pairs except the selected root. -/
theorem Valid.branch_partition {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root : V × W) (hr : root ∈ pairs) :
    pairs = insert root ((childMapping left root.1 pairs).biUnion
      (fun child => branchMapping left root.1 child.1 pairs)) := by
  classical
  ext p
  constructor
  · intro hp
    by_cases he : p = root
    · simp [he]
    · obtain ⟨child, ⟨hc, hb⟩, _⟩ := h.unique_child_branch root p hr hp he
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨child, hc, hb⟩)
  · intro hp
    rcases Finset.mem_insert.mp hp with he | hb
    · exact he ▸ hr
    · obtain ⟨child, _, hc⟩ := Finset.mem_biUnion.mp hb
      exact ((mem_branchMapping left root.1 child.1 pairs p).mp hc).1

/-- Branches associated to different selected child pairs are disjoint. -/
theorem Valid.child_branch_disjoint {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root first second : V × W)
    (hf : first ∈ childMapping left root.1 pairs) (hs : second ∈ childMapping left root.1 pairs)
    (hn : first ≠ second) :
    Disjoint (branchMapping left root.1 first.1 pairs) (branchMapping left root.1 second.1 pairs) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hfirst := (mem_childMapping left root.1 pairs first).mp hf
  have hsecond := (mem_childMapping left root.1 pairs second).mp hs
  have hfp := (mem_branchMapping left root.1 first.1 pairs p).mp hp
  have hsp := (mem_branchMapping left root.1 second.1 pairs p).mp hq
  exact hn (h.2.1.1 first hfirst.1 second hsecond.1
    (left.child_branches_disjoint hfirst.2 hsecond.2 hfp.2 hsp.2))

/-- Every additive vertex contribution decomposes exactly over the branches. -/
theorem Valid.vertex_sum_decomposition {A : Type*} [AddCommMonoid A]
    {left : FiniteTree V} {right : FiniteTree W} {pairs : Mapping V W}
    (h : Valid left right pairs) (root : V × W) (hr : root ∈ pairs) (f : V × W → A) :
    ∑ p ∈ pairs, f p = f root + ∑ child ∈ childMapping left root.1 pairs,
      ∑ p ∈ branchMapping left root.1 child.1 pairs, f p := by
  classical
  let branches := (childMapping left root.1 pairs).biUnion
    (fun child => branchMapping left root.1 child.1 pairs)
  have hn : root ∉ branches := by
    intro hm
    obtain ⟨child, hc, hb⟩ := Finset.mem_biUnion.mp hm
    exact h.root_notMem_child_branch root child hc hb
  have hp : pairs = insert root branches := h.branch_partition root hr
  conv_lhs => rw [hp, Finset.sum_insert hn]
  congr 1
  exact Finset.sum_biUnion (f := f) (fun first hf second hs hn => h.child_branch_disjoint root first second hf hs hn)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem mk_mem_mappedEdges (left : FiniteTree V) (pairs : Mapping V W) (p q : V × W) :
    s(p,q) ∈ mappedEdges left pairs ↔ p ∈ pairs ∧ q ∈ pairs ∧ left.graph.Adj p.1 q.1 := by
  classical
  rw [mappedEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
  change (p ∈ pairs ∧ q ∈ pairs) ∧ left.graph.Adj p.1 q.1 ↔ _
  exact and_assoc

/-- Every selected edge is either a root-to-child edge or lies wholly within
one child branch. This is an equality of unordered edge sets. -/
theorem Valid.edge_partition {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root : V × W) (hr : root ∈ pairs) :
    mappedEdges left pairs =
      (childMapping left root.1 pairs).image (fun child => s(root,child)) ∪
      (childMapping left root.1 pairs).biUnion
        (fun child => mappedEdges left (branchMapping left root.1 child.1 pairs)) := by
  classical
  ext edge
  refine edge.ind (fun p q => ?_)
  constructor
  · intro hm
    obtain ⟨hp, hq, hadj⟩ := (mk_mem_mappedEdges left pairs p q).mp hm
    by_cases hpr : p = root
    · subst p
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨q, (mem_childMapping left root.1 pairs q).mpr ⟨hq, hadj⟩, rfl⟩)
    by_cases hqr : q = root
    · subst q
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨p, (mem_childMapping left root.1 pairs p).mpr ⟨hp, hadj.symm⟩, Sym2.eq_swap⟩)
    obtain ⟨first, ⟨hf, hfp⟩, _⟩ := h.unique_child_branch root p hr hp hpr
    obtain ⟨second, ⟨hs, hsq⟩, _⟩ := h.unique_child_branch root q hr hq hqr
    have hfm := (mem_childMapping left root.1 pairs first).mp hf
    have hsm := (mem_childMapping left root.1 pairs second).mp hs
    have hfb := (mem_branchMapping left root.1 first.1 pairs p).mp hfp
    have hsb := (mem_branchMapping left root.1 second.1 pairs q).mp hsq
    have he : first = second := h.2.1.1 first hfm.1 second hsm.1
      (left.adjacent_same_child hfm.2 hsm.2 hfb.2 hsb.2 hadj)
    subst second
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨first, hf, (mk_mem_mappedEdges left _ p q).mpr ⟨hfp, hsq, hadj⟩⟩)
  · intro hm
    rcases Finset.mem_union.mp hm with hedge | hbranch
    · obtain ⟨child, hc, he⟩ := Finset.mem_image.mp hedge
      have hc' := (mem_childMapping left root.1 pairs child).mp hc
      rw [← he]
      exact (mk_mem_mappedEdges left pairs root child).mpr ⟨hr, hc'.1, hc'.2⟩
    · obtain ⟨child, _, he⟩ := Finset.mem_biUnion.mp hbranch
      obtain ⟨hp, hq, hadj⟩ := (mk_mem_mappedEdges left _ p q).mp he
      exact (mk_mem_mappedEdges left pairs p q).mpr
        ⟨((mem_branchMapping left root.1 child.1 pairs p).mp hp).1,
         ((mem_branchMapping left root.1 child.1 pairs q).mp hq).1, hadj⟩

omit [DecidableEq V] [DecidableEq W] in
theorem mappedEdges_disjoint (left : FiniteTree V) {first second : Mapping V W}
    (hd : Disjoint first second) : Disjoint (mappedEdges left first) (mappedEdges left second) := by
  classical
  apply Finset.disjoint_left.mpr
  intro edge
  refine edge.ind (fun p q => ?_)
  intro hfirst hsecond
  exact Finset.disjoint_left.mp hd ((mk_mem_mappedEdges left first p q).mp hfirst).1
    ((mk_mem_mappedEdges left second p q).mp hsecond).1

/-- Every additive unordered-edge contribution decomposes exactly, including
one root-to-child reward for each selected child. -/
theorem Valid.edge_sum_decomposition {A : Type*} [AddCommMonoid A]
    {left : FiniteTree V} {right : FiniteTree W} {pairs : Mapping V W}
    (h : Valid left right pairs) (root : V × W) (hr : root ∈ pairs) (f : Sym2 (V × W) → A) :
    ∑ edge ∈ mappedEdges left pairs, f edge =
      ∑ child ∈ childMapping left root.1 pairs,
        (f s(root,child) + ∑ edge ∈ mappedEdges left (branchMapping left root.1 child.1 pairs), f edge) := by
  classical
  have hd : Disjoint ((childMapping left root.1 pairs).image (fun child => s(root,child)))
      ((childMapping left root.1 pairs).biUnion
        (fun child => mappedEdges left (branchMapping left root.1 child.1 pairs))) := by
    apply Finset.disjoint_left.mpr
    intro edge he hb
    obtain ⟨child, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨other, ho, he⟩ := Finset.mem_biUnion.mp hb
    have hm := ((mk_mem_mappedEdges left _ root child).mp he).1
    exact h.root_notMem_child_branch root other ho hm
  rw [h.edge_partition root hr, Finset.sum_union hd, Finset.sum_image]
  · rw [Finset.sum_biUnion, Finset.sum_add_distrib]
    intro first hf second hs hn
    exact mappedEdges_disjoint left (h.child_branch_disjoint root first second hf hs hn)
  · intro first _ second _ he
    exact (Sym2.mkEmbedding root).injective he

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The full independent vertex/edge score splits into the mapped root reward
and the sum of its edge-plus-continuation branch rewards. -/
theorem Valid.score_decomposition {left : FiniteTree V} {right : FiniteTree W}
    {pairs : Mapping V W} (h : Valid left right pairs) (root : V × W) (hr : root ∈ pairs)
    (weights : Scoring V W K) :
    score left weights pairs = weights.node root.1 root.2 +
      ∑ child ∈ childMapping left root.1 pairs,
        (weights.edge ((s(root,child)).map Prod.fst) ((s(root,child)).map Prod.snd) +
          score left weights (branchMapping left root.1 child.1 pairs)) := by
  unfold score
  rw [h.vertex_sum_decomposition root hr, h.edge_sum_decomposition root hr]
  simp only [Finset.sum_add_distrib]
  ac_rfl

end SubtreeProofs.Droschinsky2016

end
