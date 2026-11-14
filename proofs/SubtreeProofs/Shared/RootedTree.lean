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
