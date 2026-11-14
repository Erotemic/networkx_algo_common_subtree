module

public import SubtreeProofs.Shared.FiniteTree
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Rooted geometry of independent finite trees

Ancestry uses the unique graph path, independently of any parent array or DP.
The nearest selected vertex lemma supplies the structural premise of the 2016
fixed-root reduction.
-/

@[expose] public section

namespace SubtreeProofs.FiniteTree

variable {V : Type*} (tree : FiniteTree V)

/-- A vertex is an ancestor exactly when it lies on the root-to-vertex path. -/
def Ancestor (root ancestor vertex : V) : Prop :=
  ancestor ∈ (tree.path root vertex).val.support

/-- Parent-to-child adjacency in the orientation determined by a root. -/
def Child (root parent child : V) : Prop :=
  tree.graph.Adj parent child ∧ tree.Ancestor root parent child

@[simp] theorem ancestor_refl (root vertex : V) : tree.Ancestor root vertex vertex :=
  (tree.path root vertex).val.end_mem_support

@[simp] theorem root_ancestor (root vertex : V) : tree.Ancestor root root vertex :=
  (tree.path root vertex).val.start_mem_support

/-- A proper prefix endpoint is strictly closer to the root. -/
theorem ancestor_length_lt {root u v : V} (ha : tree.Ancestor root u v) (hne : u ≠ v) :
    tree.pathLength root u < tree.pathLength root v := by
  classical
  let initialSegment : tree.graph.Path root u :=
    ⟨(tree.path root v).val.takeUntil u ha, (tree.path root v).property.takeUntil ha⟩
  have he := congrArg Subtype.val (tree.path_unique initialSegment (tree.path root u))
  unfold pathLength
  rw [← he]
  exact SimpleGraph.Walk.length_takeUntil_lt_length ha hne

theorem ancestor_length_le {root u v : V} (ha : tree.Ancestor root u v) :
    tree.pathLength root u ≤ tree.pathLength root v := by
  by_cases he : u = v
  · subst u; rfl
  · exact Nat.le_of_lt (tree.ancestor_length_lt ha he)

theorem ancestor_antisymm {root u v : V}
    (hu : tree.Ancestor root u v) (hv : tree.Ancestor root v u) : u = v := by
  by_contra hn
  have hlt := tree.ancestor_length_lt hu hn
  have hle := tree.ancestor_length_le hv
  omega

theorem ancestor_trans {root u v w : V}
    (hu : tree.Ancestor root u v) (hv : tree.Ancestor root v w) :
    tree.Ancestor root u w := by
  classical
  let initialSegment : tree.graph.Path root v :=
    ⟨(tree.path root w).val.takeUntil v hv, (tree.path root w).property.takeUntil hv⟩
  have he := congrArg Subtype.val (tree.path_unique (tree.path root v) initialSegment)
  unfold Ancestor at hu ⊢
  rw [he] at hu
  exact (tree.path root w).val.support_takeUntil_subset_support hv hu

/-- Injective graph maps between trees preserve the unique paths. -/
theorem path_map {W : Type*} (other : FiniteTree W) (f : tree.graph →g other.graph)
    (hinj : Function.Injective f) (u v : V) :
    (tree.path u v).map f hinj = other.path (f u) (f v) :=
  other.path_unique _ _

/-- Ancestry is invariant under injective tree maps. -/
theorem ancestor_map_iff {W : Type*} (other : FiniteTree W) (f : tree.graph →g other.graph)
    (hinj : Function.Injective f) (root u v : V) :
    other.Ancestor (f root) (f u) (f v) ↔ tree.Ancestor root u v := by
  have he := congrArg Subtype.val (tree.path_map other f hinj root v)
  unfold Ancestor
  rw [← he, SimpleGraph.Path.map, SimpleGraph.Walk.support_map]
  constructor
  · intro hm
    obtain ⟨x, hx, heq⟩ := List.mem_map.mp hm
    exact hinj heq ▸ hx
  · intro hm
    exact List.mem_map.mpr ⟨u, hm, rfl⟩

/-- Splitting a canonical path at an ancestor gives the two canonical paths. -/
theorem path_append_of_ancestor {root u v : V} (ha : tree.Ancestor root u v) :
    (tree.path root u).val.append (tree.path u v).val = (tree.path root v).val := by
  classical
  have hfirst := congrArg Subtype.val (tree.path_unique (tree.path root u)
    ⟨(tree.path root v).val.takeUntil u ha, (tree.path root v).property.takeUntil ha⟩)
  have hlast := congrArg Subtype.val (tree.path_unique (tree.path u v)
    ⟨(tree.path root v).val.dropUntil u ha, (tree.path root v).property.dropUntil ha⟩)
  rw [hfirst, hlast]
  exact (tree.path root v).val.take_spec ha

/-- Every point on the suffix below an ancestor remains below that ancestor. -/
theorem ancestor_of_mem_suffix {root u v x : V} (ha : tree.Ancestor root u v)
    (hx : x ∈ (tree.path u v).val.support) : tree.Ancestor root u x := by
  have hsplit := tree.path_append_of_ancestor (root := u) hx
  have hwhole : (((tree.path root u).val.append (tree.path u x).val).append
      (tree.path x v).val).IsPath := by
    rw [← SimpleGraph.Walk.append_assoc, hsplit, tree.path_append_of_ancestor ha]
    exact (tree.path root v).property
  have he := congrArg Subtype.val (tree.path_unique
    ⟨(tree.path root u).val.append (tree.path u x).val, hwhole.of_append_left⟩ (tree.path root x))
  unfold Ancestor
  rw [← he]
  exact SimpleGraph.Walk.support_subset_support_append_left _ _ (tree.path root u).val.end_mem_support

/-- Descendant regions are closed under the unique path. -/
theorem descendant_path_closed {root u x y : V}
    (hx : tree.Ancestor root u x) (hy : tree.Ancestor root u y) :
    ∀ z ∈ (tree.path x y).val.support, tree.Ancestor root u z := by
  classical
  let via := (tree.path x u).val.append (tree.path u y).val
  have he := congrArg Subtype.val (tree.path_unique (tree.path x y) via.toPath)
  intro z hz
  rw [he] at hz
  have hvia := via.support_toPath_subset_support hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hvia with hleft | hright
  · have hrev := congrArg (fun p : tree.graph.Path u x => p.val.support) (tree.path_reverse x u)
    have hmem : z ∈ (tree.path u x).val.support := by
      rw [← hrev]
      simpa using hleft
    exact tree.ancestor_of_mem_suffix hx hmem
  · exact tree.ancestor_of_mem_suffix hy hright

/-- The first edge on a nontrivial root path identifies its child branch. -/
noncomputable def firstChild (root vertex : V) : V := (tree.path root vertex).val.snd

theorem firstChild_adj {root vertex : V} (hn : root ≠ vertex) :
    tree.graph.Adj root (tree.firstChild root vertex) := by
  apply (tree.path root vertex).val.adj_snd
  intro hz
  exact hn hz.eq

theorem firstChild_ancestor {root vertex : V} :
    tree.Ancestor root (tree.firstChild root vertex) vertex :=
  (tree.path root vertex).val.getVert_mem_support 1

theorem child_ancestor_iff {root child vertex : V} (hc : tree.graph.Adj root child) :
    tree.Ancestor root child vertex ↔ child = tree.firstChild root vertex := by
  constructor
  · intro h
    exact tree.isTree.isAcyclic.eq_snd_of_adj_start (tree.path root vertex).property hc h
  · rintro rfl
    exact tree.firstChild_ancestor

/-- The endpoints of an edge are comparable in every rooted orientation. -/
theorem adjacent_ancestors (root : V) {u v : V} (ha : tree.graph.Adj u v) :
    tree.Ancestor root u v ∨ tree.Ancestor root v u := by
  by_cases hu : tree.Ancestor root u v
  · exact Or.inl hu
  · exact Or.inr (tree.isTree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      (tree.path root u).property (tree.path root v).property ha hu)

/-- Different child branches have no common vertex. -/
theorem child_branches_disjoint {root first second vertex : V}
    (hf : tree.graph.Adj root first) (hs : tree.graph.Adj root second)
    (hfirst : tree.Ancestor root first vertex) (hsecond : tree.Ancestor root second vertex) :
    first = second :=
  ((tree.child_ancestor_iff hf).mp hfirst).trans ((tree.child_ancestor_iff hs).mp hsecond).symm

/-- An edge cannot join vertices lying in different child branches. -/
theorem adjacent_same_child {root first second u v : V}
    (hf : tree.graph.Adj root first) (hs : tree.graph.Adj root second)
    (hu : tree.Ancestor root first u) (hv : tree.Ancestor root second v)
    (ha : tree.graph.Adj u v) : first = second := by
  rcases tree.adjacent_ancestors root ha with huv | hvu
  · exact tree.child_branches_disjoint hf hs (tree.ancestor_trans hu huv) hv
  · exact tree.child_branches_disjoint hf hs hu (tree.ancestor_trans hv hvu)

/-- Connected induced subsets contain the unique path between selected endpoints. -/
theorem connected_path_closed {selected : Set V}
    (hc : (tree.graph.induce selected).Connected) {u v : V}
    (hu : u ∈ selected) (hv : v ∈ selected) :
    ∀ x ∈ (tree.path u v).val.support, x ∈ selected := by
  classical
  let incl : tree.graph.induce selected →g tree.graph := ⟨Subtype.val, fun h => h⟩
  let q := (hc ⟨u,hu⟩ ⟨v,hv⟩).some.toPath
  let mapped : tree.graph.Path u v := ⟨q.val.map incl, q.property.map Subtype.val_injective⟩
  have he := congrArg Subtype.val (tree.path_unique (tree.path u v) mapped)
  intro x hx
  rw [he, SimpleGraph.Walk.support_map] at hx
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hx
  exact hy ▸ y.property

/-- The unique-path closure criterion for a connected induced subtree. -/
theorem connected_of_path_closed {selected : Set V} (hs : selected.Nonempty)
    (hclosed : ∀ u ∈ selected, ∀ v ∈ selected,
      ∀ x ∈ (tree.path u v).val.support, x ∈ selected) :
    (tree.graph.induce selected).Connected := by
  classical
  have : Nonempty selected := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  refine ⟨fun u v => ?_⟩
  exact ((tree.path u.val v.val).val.induce selected
    (hclosed u.val u.property v.val v.property)).reachable

/-- Intersecting a connected subtree with a descendant region stays connected
whenever the region's root is selected. -/
theorem connected_descendant_inter {selected : Set V}
    (hc : (tree.graph.induce selected).Connected) (root : V) {child : V} (hchild : child ∈ selected) :
    (tree.graph.induce {x | x ∈ selected ∧ tree.Ancestor root child x}).Connected := by
  refine tree.connected_of_path_closed (selected := {x | x ∈ selected ∧ tree.Ancestor root child x})
    ⟨child, hchild, tree.ancestor_refl _ _⟩ ?_
  intro u hu v hv x hx
  exact ⟨tree.connected_path_closed hc hu.1 hv.1 x hx,
    tree.descendant_path_closed hu.2 hv.2 x hx⟩

/-- A vertex minimizing distance inside a connected subtree is an ancestor of
every selected vertex. This is a structural assertion about paths, not a DP. -/
theorem nearest_is_ancestor {selected : Set V}
    (hc : (tree.graph.induce selected).Connected) (root : V) {u : V}
    (hu : u ∈ selected)
    (hmin : ∀ x ∈ selected, tree.pathLength root u ≤ tree.pathLength root x) :
    ∀ v ∈ selected, tree.Ancestor root u v := by
  classical
  intro v hv
  let p := tree.path root u
  let q := tree.path u v
  have hinter : ∀ x ∈ p.val.support, x ∈ q.val.support → x = u := by
    intro x hx hq
    by_contra hn
    have hlt := tree.ancestor_length_lt hx hn
    have hle := hmin x (tree.connected_path_closed hc hu hv x hq)
    omega
  have happ : (p.val.append q.val).IsPath := by
    apply (SimpleGraph.Walk.isPath_append p.val q.val).mpr
    refine ⟨p.property, q.property.tail, ?_⟩
    rw [List.disjoint_left]
    intro x hx hq
    have he := hinter x hx (List.mem_of_mem_tail hq)
    subst x
    have hn := q.property.support_nodup
    rw [← q.val.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1 hq
  have he := congrArg Subtype.val (tree.path_unique ⟨p.val.append q.val, happ⟩ (tree.path root v))
  unfold Ancestor
  rw [← he]
  exact SimpleGraph.Walk.support_subset_support_append_left _ _ p.val.end_mem_support

/-- Every nonempty finite connected selection has one unique top vertex. -/
theorem connected_exists_unique_top [DecidableEq V] (selected : Finset V)
    (hs : selected.Nonempty) (hc : (tree.graph.induce (selected : Set V)).Connected)
    (root : V) : ∃! u, u ∈ selected ∧ ∀ v ∈ selected, tree.Ancestor root u v := by
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image selected (tree.pathLength root) hs
  have htop := tree.nearest_is_ancestor hc root hu hmin
  refine ⟨u, ⟨hu, htop⟩, ?_⟩
  intro v hv
  exact tree.ancestor_antisymm (hv.2 u hu) (htop v hv.1)

end SubtreeProofs.FiniteTree

end
