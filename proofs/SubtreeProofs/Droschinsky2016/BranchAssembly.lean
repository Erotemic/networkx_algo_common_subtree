module

public import SubtreeProofs.Droschinsky2016.BranchDecomposition
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Assembling compatible rooted branches

Child pairs are independently injective and adjacent to the mapped root;
continuations are independent root-to-root isomorphism witnesses contained in
the corresponding descendant regions.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2016

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

structure BranchFamily (left : FiniteTree V) (right : FiniteTree W) (root : V × W) where
  children : Mapping V W
  injective : PartialBijection children
  adjacent : ∀ child ∈ children, left.graph.Adj root.1 child.1 ∧ right.graph.Adj root.2 child.2
  continuation : (V × W) → Mapping V W
  valid : ∀ child ∈ children, RootedValid left right root.1 root.2 child.1 child.2 (continuation child)

/-- A concrete union of branch witnesses, plus the mapped root. -/
def assemble (root : V × W) (children : Mapping V W) (continuation : (V × W) → Mapping V W) : Mapping V W :=
  insert root (children.biUnion continuation)

@[simp] theorem mem_assemble (root : V × W) (children : Mapping V W)
    (continuation : (V × W) → Mapping V W) (p : V × W) :
    p ∈ assemble root children continuation ↔ p = root ∨ ∃ child ∈ children, p ∈ continuation child := by
  simp [assemble]

namespace BranchFamily

variable {left : FiniteTree V} {right : FiniteTree W} {root : V × W}
  (family : BranchFamily left right root)

/-- A descendant of a child cannot be the parent root. -/
theorem descendant_ne_root {T : Type*} (tree : FiniteTree T) {r c x : T}
    (ha : tree.graph.Adj r c) (hx : tree.Ancestor r c x) : x ≠ r := by
  intro he
  subst x
  exact ha.ne (tree.ancestor_antisymm hx (tree.root_ancestor r c)).symm

/-- Projection injectivity of a branch union follows from branch disjointness
and injectivity both between child roots and within each continuation. -/
theorem projection_injective {T : Type*} (tree : FiniteTree T) (proj : V × W → T)
    (hadj : ∀ c ∈ family.children, tree.graph.Adj (proj root) (proj c))
    (hregion : ∀ c ∈ family.children, ∀ p ∈ family.continuation c,
      tree.Ancestor (proj root) (proj c) (proj p))
    (hchildren : ∀ c ∈ family.children, ∀ d ∈ family.children, proj c = proj d → c = d)
    (hlocal : ∀ c ∈ family.children, ∀ p ∈ family.continuation c,
      ∀ q ∈ family.continuation c, proj p = proj q → p = q) :
    ∀ p ∈ assemble root family.children family.continuation,
      ∀ q ∈ assemble root family.children family.continuation, proj p = proj q → p = q := by
  intro p hp q hq he
  rcases (mem_assemble _ _ _ _).mp hp with rfl | ⟨c, hc, hp⟩
  · rcases (mem_assemble _ _ _ _).mp hq with rfl | ⟨d, hd, hq⟩
    · rfl
    · exact False.elim (descendant_ne_root tree (hadj d hd) (hregion d hd q hq) he.symm)
  · rcases (mem_assemble _ _ _ _).mp hq with rfl | ⟨d, hd, hq⟩
    · exact False.elim (descendant_ne_root tree (hadj c hc) (hregion c hc p hp) he)
    · have hcp := hregion c hc p hp
      have hdq := hregion d hd q hq
      rw [he] at hcp
      have hcd := hchildren c hc d hd (tree.child_branches_disjoint (hadj c hc) (hadj d hd) hcp hdq)
      subst d
      exact hlocal c hc p hp q hq he

/-- A union of connected continuations attached by one root edge is connected.
This part uses graph connectivity, independently of acyclicity or weights. -/
theorem projection_connected {T : Type*} [DecidableEq T] (tree : FiniteTree T)
    (proj : V × W → T) (children : Mapping V W) (continuation : (V × W) → Mapping V W)
    (hadj : ∀ c ∈ children, tree.graph.Adj (proj root) (proj c))
    (hselected : ∀ c ∈ children, c ∈ continuation c)
    (hconnected : ∀ c ∈ children,
      (tree.graph.induce (↑((continuation c).image proj) : Set T)).Connected) :
    (tree.graph.induce (↑((assemble root children continuation).image proj) : Set T)).Connected := by
  induction children using Finset.induction_on with
  | empty =>
    have hs : (assemble root ∅ continuation).image proj = {proj root} := by simp [assemble]
    rw [hs, Finset.coe_singleton]
    exact SimpleGraph.Connected.of_subsingleton
  | @insert c rest hn ih =>
    have hc : c ∈ insert c rest := Finset.mem_insert_self _ _
    have hrest : ∀ d ∈ rest, d ∈ insert c rest := fun d hd => Finset.mem_insert_of_mem hd
    have hrconn := ih (fun d hd => hadj d (hrest d hd))
      (fun d hd => hselected d (hrest d hd)) (fun d hd => hconnected d (hrest d hd))
    have heq : assemble root (insert c rest) continuation =
        assemble root rest continuation ∪ continuation c := by
      ext p
      simp only [mem_assemble, Finset.mem_insert, Finset.mem_union]
      aesop
    rw [heq, Finset.image_union, Finset.coe_union]
    exact SimpleGraph.connected_induce_union hrconn.preconnected (hconnected c hc).preconnected
      (Finset.mem_image.mpr ⟨root, (mem_assemble _ _ _ _).mpr (Or.inl rfl), rfl⟩)
      (Finset.mem_image.mpr ⟨c, hselected c hc, rfl⟩) (hadj c hc)

omit [DecidableEq V] [DecidableEq W] in
/-- Within a continuation, only its own mapped root is adjacent to the parent. -/
theorem root_adj_iff {T : Type*} (tree : FiniteTree T) (proj : V × W → T)
    {c p : V × W} (hadj : tree.graph.Adj (proj root) (proj c))
    (hregion : tree.Ancestor (proj root) (proj c) (proj p))
    (hinj : proj p = proj c → p = c) : tree.graph.Adj (proj root) (proj p) ↔ p = c := by
  constructor
  · intro hp
    have he := ((tree.child_ancestor_iff hadj).mp hregion).trans
      ((tree.child_ancestor_iff hp).mp (tree.ancestor_refl _ _)).symm
    exact hinj he.symm
  · rintro rfl
    exact hadj

/-- Different matched children have no edges between their continuations. -/
theorem cross_not_adj {T : Type*} (tree : FiniteTree T) (proj : V × W → T)
    {c d p q : V × W} (hc : c ∈ family.children) (hd : d ∈ family.children)
    (hn : c ≠ d)
    (hadj : ∀ child ∈ family.children, tree.graph.Adj (proj root) (proj child))
    (hchildren : ∀ c ∈ family.children, ∀ d ∈ family.children, proj c = proj d → c = d)
    (hp : tree.Ancestor (proj root) (proj c) (proj p))
    (hq : tree.Ancestor (proj root) (proj d) (proj q)) :
    ¬ tree.graph.Adj (proj p) (proj q) := by
  intro he
  exact hn (hchildren c hc d hd (tree.adjacent_same_child (hadj c hc) (hadj d hd) hp hq he))

/-- The assembled mapping preserves adjacency in both directions. -/
theorem adjacency_preserved (p q : V × W)
    (hp : p ∈ assemble root family.children family.continuation)
    (hq : q ∈ assemble root family.children family.continuation) :
    left.graph.Adj p.1 q.1 ↔ right.graph.Adj p.2 q.2 := by
  have hroot (c : V × W) (hc : c ∈ family.children) (p : V × W)
      (hp : p ∈ family.continuation c) : left.graph.Adj root.1 p.1 ↔ right.graph.Adj root.2 p.2 := by
    have hv := family.valid c hc
    have hreg := hv.2.2 p hp
    have hl := root_adj_iff left Prod.fst (family.adjacent c hc).1 hreg.1
      (fun he => hv.1.2.1.1 p hp c hv.2.1 he)
    have hr := root_adj_iff right Prod.snd (family.adjacent c hc).2 hreg.2
      (fun he => hv.1.2.1.2 p hp c hv.2.1 he)
    exact hl.trans hr.symm
  rcases (mem_assemble _ _ _ _).mp hp with rfl | ⟨c, hc, hp⟩
  · rcases (mem_assemble _ _ _ _).mp hq with rfl | ⟨d, hd, hq⟩
    · simp
    · exact hroot d hd q hq
  · rcases (mem_assemble _ _ _ _).mp hq with rfl | ⟨d, hd, hq⟩
    · rw [left.graph.adj_comm, right.graph.adj_comm]
      exact hroot c hc p hp
    · by_cases he : c = d
      · subst d
        exact (family.valid c hc).1.2.2.2.2 p hp q hq
      · have hcp := (family.valid c hc).2.2 p hp
        have hdq := (family.valid d hd).2.2 q hq
        exact iff_of_false
          (family.cross_not_adj left Prod.fst hc hd he (fun c hc => (family.adjacent c hc).1)
            family.injective.1 hcp.1 hdq.1)
          (family.cross_not_adj right Prod.snd hc hd he (fun c hc => (family.adjacent c hc).2)
            family.injective.2 hcp.2 hdq.2)

/-- Converse structural direction: any partial matching of valid child
continuations assembles to a nonempty connected common-subtree isomorphism. -/
theorem assemble_valid : Valid left right (assemble root family.children family.continuation) := by
  refine ⟨⟨root, (mem_assemble _ _ _ _).mpr (Or.inl rfl)⟩, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact family.projection_injective left Prod.fst (fun c hc => (family.adjacent c hc).1)
        (fun c hc p hp => ((family.valid c hc).2.2 p hp).1) family.injective.1
        (fun c hc => (family.valid c hc).1.2.1.1)
    · exact family.projection_injective right Prod.snd (fun c hc => (family.adjacent c hc).2)
        (fun c hc p hp => ((family.valid c hc).2.2 p hp).2) family.injective.2
        (fun c hc => (family.valid c hc).1.2.1.2)
  · exact projection_connected left Prod.fst family.children family.continuation
      (fun c hc => (family.adjacent c hc).1) (fun c hc => (family.valid c hc).2.1)
      (fun c hc => (family.valid c hc).1.2.2.1)
  · exact projection_connected right Prod.snd family.children family.continuation
      (fun c hc => (family.adjacent c hc).2) (fun c hc => (family.valid c hc).2.1)
      (fun c hc => (family.valid c hc).1.2.2.2.1)
  · intro p hp q hq
    exact family.adjacency_preserved p q hp hq

/-- Assembly reconstructs exactly the selected child matching. -/
theorem childMapping_assemble :
    childMapping left root.1 (assemble root family.children family.continuation) = family.children := by
  ext p
  constructor
  · intro hp
    have hm := (mem_childMapping left root.1 _ p).mp hp
    rcases (mem_assemble _ _ _ _).mp hm.1 with he | ⟨c, hc, hp⟩
    · subst p
      exact False.elim (hm.2.ne rfl)
    · have hv := family.valid c hc
      have he := (root_adj_iff left Prod.fst (family.adjacent c hc).1 (hv.2.2 p hp).1
        (fun he => hv.1.2.1.1 p hp c hv.2.1 he)).mp hm.2
      exact he ▸ hc
  · intro hp
    exact (mem_childMapping left root.1 _ p).mpr
      ⟨(mem_assemble _ _ _ _).mpr (Or.inr ⟨p, hp, (family.valid p hp).2.1⟩), (family.adjacent p hp).1⟩

/-- Restriction of an assembled witness recovers each supplied continuation. -/
theorem branchMapping_assemble (c : V × W) (hc : c ∈ family.children) :
    branchMapping left root.1 c.1 (assemble root family.children family.continuation) = family.continuation c := by
  ext p
  constructor
  · intro hp
    have hm := (mem_branchMapping left root.1 c.1 _ p).mp hp
    rcases (mem_assemble _ _ _ _).mp hm.1 with he | ⟨d, hd, hp⟩
    · have hn := descendant_ne_root left (family.adjacent c hc).1 hm.2
      exact False.elim (hn (congrArg Prod.fst he))
    · have hreg := ((family.valid d hd).2.2 p hp).1
      have he := family.injective.1 c hc d hd
        (left.child_branches_disjoint (family.adjacent c hc).1 (family.adjacent d hd).1 hm.2 hreg)
      subst d
      exact hp
  · intro hp
    exact (mem_branchMapping left root.1 c.1 _ p).mpr
      ⟨(mem_assemble _ _ _ _).mpr (Or.inr ⟨c, hc, hp⟩), ((family.valid c hc).2.2 p hp).1⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Exact independent score of an assembled branch family. -/
theorem score_assemble (weights : Scoring V W K) :
    score left weights (assemble root family.children family.continuation) = weights.node root.1 root.2 +
      ∑ child ∈ family.children,
        (weights.edge ((s(root,child)).map Prod.fst) ((s(root,child)).map Prod.snd) +
          score left weights (family.continuation child)) := by
  have hs := family.assemble_valid.score_decomposition root
    ((mem_assemble _ _ _ _).mpr (Or.inl rfl)) weights
  rw [family.childMapping_assemble] at hs
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  rw [family.branchMapping_assemble c hc]

end BranchFamily

end SubtreeProofs.Droschinsky2016

end
