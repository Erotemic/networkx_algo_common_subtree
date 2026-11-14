module

public import SubtreeProofs.Droschinsky2018.Witness
public import SubtreeProofs.Shared.RootedEmbedding

/-!
# Recovering a skeleton from explicit topological realizations

The selected-image skeleton is exactly the abstract tree, rather than an
additional assumption on a realization. This bridges explicit independent
edge-path witnesses back to the finite pair specification.
-/

@[expose] public section

namespace SubtreeProofs.TopologicalEmbedding

open Droschinsky2016 Droschinsky2018

variable {A V : Type*} [Fintype A] [DecidableEq V]
  {common : FiniteTree A} {target : FiniteTree V}

/-- The finite image of an explicit common-tree realization. -/
noncomputable def selected (embedding : TopologicalEmbedding common target) : Finset V := by
  classical
  exact Finset.univ.image embedding.map

@[simp] theorem mem_selected (embedding : TopologicalEmbedding common target) (x : V) :
    x ∈ embedding.selected ↔ ∃ a, embedding.map a = x := by
  classical
  simp [selected]

/-- Abstract edges are precisely consecutive selected target vertices. -/
theorem adjacency_iff_branchAdjacent (embedding : TopologicalEmbedding common target) (a b : A) :
    common.graph.Adj a b ↔ BranchAdjacent target embedding.selected (embedding.map a) (embedding.map b) := by
  classical
  constructor
  · intro ha
    refine ⟨fun he => ha.ne (embedding.injective he), ?_⟩
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨c, rfl⟩ := (embedding.mem_selected x).mp hs
    exact embedding.avoids_vertices a b ha c hx
  · rintro ⟨hne, hd⟩
    by_contra ha
    have hab : a ≠ b := fun he => hne (congrArg embedding.map he)
    let path := common.path a b
    let c := common.firstChild a b
    have hac := common.firstChild_adj hab
    have hca : c ≠ a := hac.ne.symm
    have hcb : c ≠ b := by intro he; exact ha (he ▸ hac)
    have hc : c ∈ path.val.support := common.firstChild_ancestor
    have hm : embedding.map c ∈ (target.path (embedding.map a) (embedding.map b)).val.support := by
      rw [← embedding.lift_path a b]
      exact (embedding.liftWalk_mapped_mem path.val c).mpr hc
    have hxi : embedding.map c ∈ target.pathInterior (embedding.map a) (embedding.map b) :=
      Finset.mem_erase.mpr ⟨fun he => hcb (embedding.injective he),
        Finset.mem_erase.mpr ⟨fun he => hca (embedding.injective he), List.mem_toFinset.mpr hm⟩⟩
    exact Finset.disjoint_left.mp hd hxi ((embedding.mem_selected _).mpr ⟨c, rfl⟩)

/-- Abstract vertices and selected target vertices are in canonical bijection. -/
noncomputable def selectedEquiv (embedding : TopologicalEmbedding common target) :
    A ≃ ↑(embedding.selected : Set V) :=
  Equiv.ofBijective (fun a => ⟨embedding.map a, (embedding.mem_selected _).mpr ⟨a, rfl⟩⟩) (by
    constructor
    · intro a b he
      exact embedding.injective (congrArg Subtype.val he)
    · intro vertex
      obtain ⟨a, ha⟩ := (embedding.mem_selected vertex.val).mp vertex.property
      exact ⟨a, Subtype.ext ha⟩)

/-- The image skeleton is isomorphic to the independently given common tree. -/
noncomputable def selectedIso (embedding : TopologicalEmbedding common target) :
    common.graph ≃g skeleton target embedding.selected where
  toEquiv := embedding.selectedEquiv
  map_rel_iff' := by
    intro a b
    exact (embedding.adjacency_iff_branchAdjacent a b).symm

theorem selected_isTree (embedding : TopologicalEmbedding common target) :
    (skeleton target embedding.selected).IsTree :=
  embedding.selectedIso.isTree_iff.mp common.isTree

/-- The selected image satisfies the independent skeleton interior condition. -/
theorem selected_interiorDisjoint (embedding : TopologicalEmbedding common target) :
    InteriorDisjoint target embedding.selected := by
  classical
  intro first
  refine first.ind (fun x y => ?_)
  intro hfirst second
  refine second.ind (fun z w => ?_)
  intro hsecond hn
  rw [skeletonEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff] at hfirst hsecond
  obtain ⟨a, rfl⟩ := (embedding.mem_selected x).mp hfirst.1.1
  obtain ⟨b, rfl⟩ := (embedding.mem_selected y).mp hfirst.1.2
  obtain ⟨c, rfl⟩ := (embedding.mem_selected z).mp hsecond.1.1
  obtain ⟨d, rfl⟩ := (embedding.mem_selected w).mp hsecond.1.2
  have hab := (embedding.adjacency_iff_branchAdjacent a b).mpr hfirst.2
  have hcd := (embedding.adjacency_iff_branchAdjacent c d).mpr hsecond.2
  apply embedding.interior_disjoint a b hab c d hcd
  intro he
  exact hn (congrArg (Sym2.map embedding.map) he)

end SubtreeProofs.TopologicalEmbedding

namespace SubtreeProofs.Droschinsky2018

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

open Droschinsky2016

variable {A V W : Type*} [Fintype A] [DecidableEq V] [DecidableEq W]
  {common : FiniteTree A} {left : FiniteTree V} {right : FiniteTree W}

/-- The concrete partial mapping induced by two explicit realizations. -/
noncomputable def pairedImage (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) : Mapping V W := by
  classical
  exact Finset.univ.image (fun a => (first.map a, second.map a))

@[simp] theorem mem_pairedImage (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) (x : V) (y : W) :
    (x,y) ∈ pairedImage first second ↔ ∃ a, first.map a = x ∧ second.map a = y := by
  classical
  simp [pairedImage]

@[simp] theorem pairedImage_fst (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) :
    (pairedImage first second).image Prod.fst = first.selected := by
  classical
  simp only [pairedImage, Finset.image_image, TopologicalEmbedding.selected, Function.comp_def]

@[simp] theorem pairedImage_snd (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) :
    (pairedImage first second).image Prod.snd = second.selected := by
  classical
  simp only [pairedImage, Finset.image_image, TopologicalEmbedding.selected, Function.comp_def]

/-- Any pair of explicit common-tree realizations yields a valid independent
skeleton witness; the tree and interior conditions are derived, not assumed. -/
theorem pairedImage_valid (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) : Valid left right (pairedImage first second) := by
  classical
  obtain ⟨a⟩ := common.isTree.connected.nonempty
  refine ⟨⟨(first.map a, second.map a), (mem_pairedImage _ _ _ _).mpr ⟨a, rfl, rfl⟩⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro p hp q hq he
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
      exact congrArg (fun a => (first.map a, second.map a)) (first.injective he)
    · intro p hp q hq he
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
      exact congrArg (fun a => (first.map a, second.map a)) (second.injective he)
  · rw [pairedImage_fst]
    exact first.selected_isTree
  · rw [pairedImage_snd]
    exact second.selected_isTree
  · rw [pairedImage_fst]
    exact first.selected_interiorDisjoint
  · rw [pairedImage_snd]
    exact second.selected_interiorDisjoint
  · intro p hp q hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    rw [pairedImage_fst, pairedImage_snd]
    exact (first.adjacency_iff_branchAdjacent a b).symm.trans (second.adjacency_iff_branchAdjacent a b)

omit [DecidableEq W] in
@[simp] theorem mk_mem_mappedEdges (tree : FiniteTree V) (pairs : Mapping V W) (p q : V × W) :
    s(p,q) ∈ mappedEdges tree pairs ↔ p ∈ pairs ∧ q ∈ pairs ∧
      BranchAdjacent tree (pairs.image Prod.fst) p.1 q.1 := by
  classical
  rw [mappedEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
  change (p ∈ pairs ∧ q ∈ pairs) ∧ BranchAdjacent tree (pairs.image Prod.fst) p.1 q.1 ↔ _
  exact and_assoc

/-- All unordered edges of the explicit common tree. Classical decidability
is local to the finite enumeration, not an additional theorem hypothesis. -/
noncomputable def commonEdges (common : FiniteTree A) : Finset (Sym2 A) := by
  classical
  exact common.graph.edgeFinset

@[simp] theorem mk_mem_commonEdges (common : FiniteTree A) (a b : A) :
    s(a,b) ∈ commonEdges common ↔ common.graph.Adj a b := by
  classical
  rw [commonEdges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

/-- The abstract tree's edge set is precisely the concrete mapped skeleton
edge set, with unordered edges mapped once. -/
theorem pairedImage_edges (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) :
    mappedEdges left (pairedImage first second) = (commonEdges common).image
      (Sym2.map (fun a => (first.map a, second.map a))) := by
  classical
  ext edge
  refine edge.ind (fun p q => ?_)
  constructor
  · intro he
    obtain ⟨hp, hq, ha⟩ := (mk_mem_mappedEdges left _ p q).mp he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    rw [pairedImage_fst] at ha
    exact Finset.mem_image.mpr ⟨s(a,b),
      (mk_mem_commonEdges common a b).mpr
        ((first.adjacency_iff_branchAdjacent a b).mpr ha), rfl⟩
  · intro he
    obtain ⟨abstractEdge, he, heq⟩ := Finset.mem_image.mp he
    rw [← heq]
    revert he
    refine abstractEdge.ind (fun a b => ?_)
    intro he
    have ha := (mk_mem_commonEdges common a b).mp he
    apply (mk_mem_mappedEdges left _ _ _).mpr
    refine ⟨(mem_pairedImage _ _ _ _).mpr ⟨a, rfl, rfl⟩,
      (mem_pairedImage _ _ _ _).mpr ⟨b, rfl, rfl⟩, ?_⟩
    rw [pairedImage_fst]
    exact (first.adjacency_iff_branchAdjacent a b).mp ha

/-- The source-style score over explicit abstract vertices and edges. -/
noncomputable def realizationScore (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) (weights : Scoring V W K) (penalty : WithTop K) : WithBot K := by
  classical
  exact (∑ a, weights.node (first.map a) (second.map a)) +
    ∑ edge ∈ commonEdges common, pathScore left right weights penalty
      (edge.map first.map) (edge.map second.map)

omit [IsStrictOrderedRing K] in
/-- Vertex and unordered-edge scores agree exactly across witness formats. -/
theorem score_pairedImage (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) (weights : Scoring V W K) (penalty : WithTop K) :
    score left right weights penalty (pairedImage first second) = realizationScore first second weights penalty := by
  classical
  have hinj : Function.Injective (fun a => (first.map a, second.map a)) :=
    fun a b he => first.injective (congrArg Prod.fst he)
  have hnode : (∑ p ∈ pairedImage first second, weights.node p.1 p.2) =
      ∑ a, weights.node (first.map a) (second.map a) := by
    rw [pairedImage, Finset.sum_image]
    exact fun a _ b _ he => hinj he
  unfold score realizationScore
  rw [hnode, pairedImage_edges, Finset.sum_image]
  · congr 1
    apply Finset.sum_congr rfl
    intro edge _
    rw [Sym2.map_map, Sym2.map_map]
    rfl
  · exact fun a _ b _ he => Sym2.map.injective hinj he

/-- Reindexing the common tree by an isomorphism leaves the concrete pair
relation unchanged. -/
theorem pairedImage_precomposeIso {B : Type*} [Fintype B] (other : FiniteTree B)
    (iso : other.graph ≃g common.graph) (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) :
    pairedImage (first.precompose iso) (second.precompose iso) = pairedImage first second := by
  ext p
  constructor
  · intro hp
    obtain ⟨b, hb, hc⟩ := (mem_pairedImage _ _ p.1 p.2).mp hp
    exact (mem_pairedImage _ _ p.1 p.2).mpr ⟨iso b, hb, hc⟩
  · intro hp
    obtain ⟨a, ha, hb⟩ := (mem_pairedImage _ _ p.1 p.2).mp hp
    obtain ⟨b, rfl⟩ := iso.surjective a
    exact (mem_pairedImage _ _ p.1 p.2).mpr ⟨b, ha, hb⟩

omit [IsStrictOrderedRing K] in
/-- The abstract common-tree score is invariant under common-tree isomorphism. -/
theorem realizationScore_precomposeIso {B : Type*} [Fintype B] (other : FiniteTree B)
    (iso : other.graph ≃g common.graph) (first : TopologicalEmbedding common left)
    (second : TopologicalEmbedding common right) (weights : Scoring V W K) (penalty : WithTop K) :
    realizationScore (first.precompose iso) (second.precompose iso) weights penalty =
      realizationScore first second weights penalty := by
  calc
    _ = score left right weights penalty (pairedImage (first.precompose iso) (second.precompose iso)) :=
      (score_pairedImage _ _ _ _).symm
    _ = score left right weights penalty (pairedImage first second) :=
      congrArg (score left right weights penalty) (pairedImage_precomposeIso other iso first second)
    _ = _ := score_pairedImage _ _ _ _

omit [IsStrictOrderedRing K] in
/-- Source Definition 1 embeddings in both input trees induce exactly the
independent finite-pair witness and its vertex/path score. Root-to-root is
optional, as in Definition 2's general CSE. -/
theorem rooted_source_witness {commonRoot : A} {leftRoot : V} {rightRoot : W}
    (first : RootedTopologicalEmbedding common left commonRoot leftRoot)
    (second : RootedTopologicalEmbedding common right commonRoot rightRoot)
    (weights : Scoring V W K) (penalty : WithTop K) :
    Valid left right (pairedImage first.toUnrooted second.toUnrooted) ∧
      score left right weights penalty (pairedImage first.toUnrooted second.toUnrooted) =
        realizationScore first.toUnrooted second.toUnrooted weights penalty :=
  ⟨pairedImage_valid _ _, score_pairedImage _ _ _ _⟩

/-- Extracting the two realizations and recombining them preserves every pair. -/
theorem Valid.realizations_roundtrip [Fintype V] [Fintype W]
    {pairs : Mapping V W} (h : Valid left right pairs) :
    pairedImage h.leftEmbedding h.rightEmbedding = pairs := by
  ext p
  exact (mem_pairedImage _ _ p.1 p.2).trans (h.embedding_pairs p.1 p.2).symm

/-- Exact unrooted correspondence with the two local clauses of source
Definitions 1--2. The finite common carrier is canonically reindexed by the
selected left vertices. Corresponding roots are existential here; fixed
ambient-root admissibility remains a distinct restriction. -/
theorem valid_iff_source_embeddings [Fintype V] [Fintype W] (pairs : Mapping V W) :
    Valid left right pairs ↔
      ∃ (source : FiniteTree (LeftVertices pairs)) (sourceRoot : LeftVertices pairs)
        (leftRoot : V) (rightRoot : W)
        (first : RootedTopologicalEmbedding source left sourceRoot leftRoot)
        (second : RootedTopologicalEmbedding source right sourceRoot rightRoot),
        pairedImage first.toUnrooted second.toUnrooted = pairs := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.1
    let root : LeftVertices pairs := ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    refine ⟨h.commonTree, root, h.leftEmbedding.map root, h.rightEmbedding.map root,
      h.leftEmbedding.toRooted root, h.rightEmbedding.toRooted root, ?_⟩
    change pairedImage h.leftEmbedding h.rightEmbedding = pairs
    exact h.realizations_roundtrip
  · rintro ⟨source, root, leftRoot, rightRoot, first, second, he⟩
    rw [← he]
    exact pairedImage_valid _ _

end SubtreeProofs.Droschinsky2018

end
