module

public import SubtreeProofs.Shared.RootedTree
public import Mathlib.Data.Sym.Sym2

/-!
# Unrooted topological tree realizations

An abstract tree maps injectively to vertices of a target tree. Each abstract
edge is realized by the target's unique path; no abstract vertex lies in an
edge interior, and distinct abstract edges have disjoint interiors. Rooted
ancestry is an additional condition, not assumed by this unrooted carrier.
-/

@[expose] public section

namespace SubtreeProofs

structure TopologicalEmbedding {A V : Type*} [DecidableEq V]
    (common : FiniteTree A) (target : FiniteTree V) where
  map : A → V
  injective : Function.Injective map
  avoids_vertices : ∀ a b, common.graph.Adj a b → ∀ c,
    map c ∉ target.pathInterior (map a) (map b)
  interior_disjoint : ∀ a b, common.graph.Adj a b → ∀ c d, common.graph.Adj c d →
    s(a,b) ≠ s(c,d) →
      Disjoint (target.pathInterior (map a) (map b)) (target.pathInterior (map c) (map d))

namespace TopologicalEmbedding

variable {A B V : Type*} [DecidableEq V]
  {first : FiniteTree A} {second : FiniteTree B} {target : FiniteTree V}

@[ext] theorem ext {one two : TopologicalEmbedding first target} (he : one.map = two.map) : one = two := by
  cases one
  cases two
  cases he
  rfl

/-- Restriction along any injective graph map between common trees. -/
def precomposeHom (embedding : TopologicalEmbedding second target) (f : first.graph →g second.graph)
    (hinj : Function.Injective f) : TopologicalEmbedding first target where
  map := embedding.map ∘ f
  injective := embedding.injective.comp hinj
  avoids_vertices := fun a b hab c => embedding.avoids_vertices (f a) (f b) (f.map_rel hab) (f c)
  interior_disjoint := by
    intro a b hab c d hcd hn
    apply embedding.interior_disjoint (f a) (f b) (f.map_rel hab) (f c) (f d) (f.map_rel hcd)
    intro he
    exact hn (Sym2.map.injective hinj he)

/-- Reindexing the abstract common tree preserves its path realization. -/
def precompose (embedding : TopologicalEmbedding second target) (iso : first.graph ≃g second.graph) :
    TopologicalEmbedding first target := embedding.precomposeHom iso.toHom iso.injective

/-- Every abstract edge has a nontrivial target path. -/
theorem edge_length_pos (embedding : TopologicalEmbedding first target) {a b : A}
    (ha : first.graph.Adj a b) : 0 < target.pathLength (embedding.map a) (embedding.map b) :=
  target.pathLength_pos (fun he => ha.ne (embedding.injective he))

/-- Distinct realized edges can meet only at endpoints of each edge. -/
theorem edge_intersection_endpoint (embedding : TopologicalEmbedding first target)
    {a b c d : A} (hab : first.graph.Adj a b) (hcd : first.graph.Adj c d)
    (hn : s(a,b) ≠ s(c,d)) {x : V}
    (hx : x ∈ target.pathVertices (embedding.map a) (embedding.map b))
    (hy : x ∈ target.pathVertices (embedding.map c) (embedding.map d)) :
    x = embedding.map a ∨ x = embedding.map b := by
  by_contra hne
  have hxa : x ≠ embedding.map a := fun he => hne (Or.inl he)
  have hxb : x ≠ embedding.map b := fun he => hne (Or.inr he)
  have hxi : x ∈ target.pathInterior (embedding.map a) (embedding.map b) := by
    exact Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hx⟩⟩
  have hxc : x ≠ embedding.map c := by
    intro he
    exact embedding.avoids_vertices a b hab c (he ▸ hxi)
  have hxd : x ≠ embedding.map d := by
    intro he
    exact embedding.avoids_vertices a b hab d (he ▸ hxi)
  have hyi : x ∈ target.pathInterior (embedding.map c) (embedding.map d) :=
    Finset.mem_erase.mpr ⟨hxd, Finset.mem_erase.mpr ⟨hxc, hy⟩⟩
  exact Finset.disjoint_left.mp (embedding.interior_disjoint a b hab c d hcd hn) hxi hyi

/-- The branch paths at a mapped vertex have exactly that vertex in common.
This is the path-disjointness clause of 2018 Definition 1, before imposing a
rooted orientation on the realization. -/
theorem branch_paths_intersection (embedding : TopologicalEmbedding first target)
    {a b c : A} (hab : first.graph.Adj a b) (hac : first.graph.Adj a c) (hn : b ≠ c) (x : V) :
    (x ∈ target.pathVertices (embedding.map a) (embedding.map b) ∧
      x ∈ target.pathVertices (embedding.map a) (embedding.map c)) ↔ x = embedding.map a := by
  constructor
  · rintro ⟨hx, hy⟩
    have hne : s(a,b) ≠ s(a,c) := fun he => hn ((Sym2.mkEmbedding a).injective he)
    have hfirst := embedding.edge_intersection_endpoint hab hac hne hx hy
    have hsecond := embedding.edge_intersection_endpoint hac hab hne.symm hy hx
    rcases hfirst with he | he
    · exact he
    rcases hsecond with he' | he'
    · exact he'
    · exact False.elim (hn (embedding.injective (he.symm.trans he')))
  · rintro rfl
    exact ⟨List.mem_toFinset.mpr (target.path (embedding.map a) (embedding.map b)).val.start_mem_support,
      List.mem_toFinset.mpr (target.path (embedding.map a) (embedding.map c)).val.start_mem_support⟩

/-- Lift an abstract walk by replacing each abstract edge by its actual
canonical target path. -/
noncomputable def liftWalk (embedding : TopologicalEmbedding first target) {a b : A} :
    first.graph.Walk a b → target.graph.Walk (embedding.map a) (embedding.map b)
  | .nil => .nil
  | .cons _hab rest => (target.path _ _).val.append (embedding.liftWalk rest)

/-- A mapped abstract vertex lies on a realized edge exactly at an endpoint. -/
theorem mapped_vertex_on_edge (embedding : TopologicalEmbedding first target)
    {a b c : A} (hab : first.graph.Adj a b) :
    embedding.map c ∈ target.pathVertices (embedding.map a) (embedding.map b) ↔ c = a ∨ c = b := by
  constructor
  · intro hc
    by_contra hn
    have hca : embedding.map c ≠ embedding.map a := fun he => hn (Or.inl (embedding.injective he))
    have hcb : embedding.map c ≠ embedding.map b := fun he => hn (Or.inr (embedding.injective he))
    exact embedding.avoids_vertices a b hab c
      (Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, hc⟩⟩)
  · rintro (rfl | rfl)
    · exact List.mem_toFinset.mpr (target.path _ _).val.start_mem_support
    · exact List.mem_toFinset.mpr (target.path _ _).val.end_mem_support

/-- Lifting neither loses abstract vertices nor introduces another mapped
abstract vertex into a path interior. -/
theorem liftWalk_mapped_mem (embedding : TopologicalEmbedding first target)
    {a b : A} (walk : first.graph.Walk a b) (c : A) :
    embedding.map c ∈ (embedding.liftWalk walk).support ↔ c ∈ walk.support := by
  induction walk with
  | nil => simp [liftWalk, embedding.injective.eq_iff]
  | @cons a b z hab rest ih =>
    rw [liftWalk, SimpleGraph.Walk.mem_support_append_iff]
    have hedge : embedding.map c ∈ (target.path (embedding.map a) (embedding.map b)).val.support ↔
        c = a ∨ c = b := by
      exact (List.mem_toFinset.symm).trans (embedding.mapped_vertex_on_edge hab)
    rw [hedge, ih, SimpleGraph.Walk.support_cons, List.mem_cons]
    have hb := rest.start_mem_support
    aesop

/-- Every target vertex in a lifted walk is either its starting image or lies
on the realization of one of its abstract edges. -/
theorem liftWalk_support_cases (embedding : TopologicalEmbedding first target)
    {a b : A} (walk : first.graph.Walk a b) {x : V}
    (hx : x ∈ (embedding.liftWalk walk).support) :
    x = embedding.map a ∨ ∃ c d, first.graph.Adj c d ∧ c ∈ walk.support ∧ d ∈ walk.support ∧
      x ∈ target.pathVertices (embedding.map c) (embedding.map d) := by
  induction walk with
  | nil => exact Or.inl (by simpa [liftWalk] using hx)
  | @cons a b z hab rest ih =>
    rw [liftWalk, SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hedge | hrest
    · exact Or.inr ⟨a, b, hab, by simp, by simp [rest.start_mem_support], List.mem_toFinset.mpr hedge⟩
    · rcases ih hrest with he | ⟨c, d, hcd, hc, hd, he⟩
      · exact Or.inr ⟨a, b, hab, by simp, by simp [rest.start_mem_support],
          he ▸ List.mem_toFinset.mpr (target.path _ _).val.end_mem_support⟩
      · exact Or.inr ⟨c, d, hcd, by simp [hc], by simp [hd], he⟩

/-- A simple abstract path lifts to a simple target path. -/
theorem liftWalk_isPath (embedding : TopologicalEmbedding first target)
    {a b : A} (walk : first.graph.Walk a b) (hw : walk.IsPath) :
    (embedding.liftWalk walk).IsPath := by
  induction walk with
  | nil => simp [liftWalk]
  | @cons a b z hab rest ih =>
    have hpath := (SimpleGraph.Walk.cons_isPath_iff hab rest).mp hw
    have hrest := ih hpath.1
    rw [liftWalk]
    apply (SimpleGraph.Walk.isPath_append _ _).mpr
    refine ⟨(target.path _ _).property, hrest.tail, ?_⟩
    rw [List.disjoint_left]
    intro x hx htail
    have hwhole := List.mem_of_mem_tail htail
    have hend : x = embedding.map a ∨ x = embedding.map b := by
      rcases embedding.liftWalk_support_cases rest hwhole with he | ⟨c, d, hcd, hc, hd, hedge⟩
      · exact Or.inr he
      · have hne : s(a,b) ≠ s(c,d) := by
          intro he
          have hm : a ∈ s(c,d) := he ▸ Sym2.mem_mk_left a b
          rcases Sym2.mem_iff.mp hm with he | he
          · subst c; exact hpath.2 hc
          · subst d; exact hpath.2 hd
        exact embedding.edge_intersection_endpoint hab hcd hne (List.mem_toFinset.mpr hx) hedge
    rcases hend with he | he
    · exact hpath.2 ((embedding.liftWalk_mapped_mem rest a).mp (he ▸ hwhole))
    · have hn := hrest.support_nodup
      rw [← (embedding.liftWalk rest).cons_tail_support] at hn
      exact (List.nodup_cons.mp hn).1 (he ▸ htail)

/-- The lifted canonical path is the canonical target path. -/
theorem lift_path (embedding : TopologicalEmbedding first target) (a b : A) :
    embedding.liftWalk (first.path a b).val = (target.path (embedding.map a) (embedding.map b)).val :=
  congrArg Subtype.val (target.path_unique
    ⟨_, embedding.liftWalk_isPath _ (first.path a b).property⟩ (target.path _ _))

/-- Topological realizations preserve and reflect rooted ancestry when the
chosen abstract root maps to the chosen target root. -/
theorem ancestor_iff (embedding : TopologicalEmbedding first target) (root a b : A) :
    target.Ancestor (embedding.map root) (embedding.map a) (embedding.map b) ↔
      first.Ancestor root a b := by
  unfold FiniteTree.Ancestor
  rw [← embedding.lift_path root b]
  exact embedding.liftWalk_mapped_mem _ _

end TopologicalEmbedding
/-- The two clauses of 2018 Definition 1 on rooted trees. Root-to-root
preservation is a separate property, as in the source. -/
structure RootedTopologicalEmbedding {A V : Type*} [DecidableEq V]
    (common : FiniteTree A) (target : FiniteTree V) (commonRoot : A) (targetRoot : V) where
  map : A → V
  injective : Function.Injective map
  downward : ∀ a b, common.Child commonRoot a b → target.Ancestor targetRoot (map a) (map b)
  branches : ∀ a b c, common.Child commonRoot a b → common.Child commonRoot a c → b ≠ c →
    ∀ x, (x ∈ target.pathVertices (map a) (map b) ∧ x ∈ target.pathVertices (map a) (map c)) ↔ x = map a

namespace RootedTopologicalEmbedding

variable {A V : Type*} [DecidableEq V]
  {common : FiniteTree A} {target : FiniteTree V} {commonRoot : A} {targetRoot : V}

/-- The explicit root-mapping requirement of the source root-to-root variant. -/
def RootToRoot (embedding : RootedTopologicalEmbedding common target commonRoot targetRoot) : Prop :=
  embedding.map commonRoot = targetRoot

end RootedTopologicalEmbedding

namespace TopologicalEmbedding

variable {A V : Type*} [DecidableEq V] {common : FiniteTree A} {target : FiniteTree V}

/-- Every unrooted realization satisfies the source rooted conditions when
rooted at corresponding vertices. -/
def toRooted (embedding : TopologicalEmbedding common target) (root : A) :
    RootedTopologicalEmbedding common target root (embedding.map root) where
  map := embedding.map
  injective := embedding.injective
  downward := fun a b hab => (embedding.ancestor_iff root a b).mpr hab.2
  branches := fun _ _ _ hab hac hn => embedding.branch_paths_intersection hab.1 hac.1 hn

@[simp] theorem toRooted_rootToRoot (embedding : TopologicalEmbedding common target) (root : A) :
    (embedding.toRooted root).RootToRoot := rfl

end TopologicalEmbedding

end SubtreeProofs

end
