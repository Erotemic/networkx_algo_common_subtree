module

public import SubtreeProofs.Paper2004.OrderedIsomorphism
public import Mathlib.Data.Tree.Basic
import Mathlib.Tactic

/-! # Ordered isomorphism retaining original vertex identities

An annotated binary word is a first-child/next-sibling forest. The independent
operation deletes a whole child subtree at any context; it never promotes
grandchildren. Labels are original identities, not affinities. Operational
pruning is proved equivalent to structural ordered selection, and erasure
refines the established unlabelled adjacency-preserving specification.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.AnnotatedIso

abbrev Word (α : Type*) := BinaryTree α

inductive DropStep {α : Type*} : Word α → Word α → Prop where
  | root (label : α) (head tail : Word α) : DropStep (.node label head tail) tail
  | head (label : α) (tail : Word α) {before after : Word α} : DropStep before after →
      DropStep (.node label before tail) (.node label after tail)
  | tail (label : α) (head : Word α) {before after : Word α} : DropStep before after →
      DropStep (.node label head before) (.node label head after)

def Prunes {α : Type*} (small large : Word α) : Prop := Relation.ReflTransGen DropStep large small

/-- A structural view of the independent whole-subtree deletion closure. -/
inductive Select {α : Type*} : Word α → Word α → Prop where
  | nil (large : Word α) : Select .nil large
  | skip (label : α) (head : Word α) {small tail : Word α} : Select small tail →
      Select small (.node label head tail)
  | keep {label : α} {smallHead largeHead smallTail largeTail : Word α} :
      Select smallHead largeHead → Select smallTail largeTail →
        Select (.node label smallHead smallTail) (.node label largeHead largeTail)

theorem Select.refl {α : Type*} (word : Word α) : Select word word := by
  induction word with
  | nil => exact .nil _
  | node label head tail ihHead ihTail => exact .keep ihHead ihTail

theorem Select.trans {α : Type*} {small middle large : Word α}
    (hSmall : Select small middle) (hLarge : Select middle large) : Select small large := by
  induction hLarge generalizing small with
  | nil => cases hSmall; exact .nil _
  | skip label head _ ih => exact .skip label head (ih hSmall)
  | keep _ _ ihHead ihTail =>
    cases hSmall with
    | nil => exact .nil _
    | skip label head rest => exact .skip _ _ (ihTail rest)
    | keep head tail => exact .keep (ihHead head) (ihTail tail)

theorem Prunes.empty {α : Type*} (word : Word α) : Prunes .nil word := by
  induction word with
  | nil => exact .refl
  | node label head tail _ ihTail =>
    exact (Relation.ReflTransGen.single (DropStep.root label head tail)).trans ihTail

theorem Prunes.head {α : Type*} {small large : Word α} (h : Prunes small large)
    (label : α) (tail : Word α) : Prunes (.node label small tail) (.node label large tail) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.head label tail step)

theorem Prunes.tail {α : Type*} {small large : Word α} (h : Prunes small large)
    (label : α) (head : Word α) : Prunes (.node label head small) (.node label head large) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (DropStep.tail label head step)

theorem Select.prunes {α : Type*} {small large : Word α} (h : Select small large) : Prunes small large := by
  induction h with
  | nil large => exact Prunes.empty large
  | skip label head _ ih =>
    exact (Relation.ReflTransGen.single (DropStep.root label head _)).trans ih
  | keep head tail ihHead ihTail => exact (ihHead.head _ _).trans (ihTail.tail _ _)

theorem DropStep.select {α : Type*} {before after : Word α} (h : DropStep before after) : Select after before := by
  induction h with
  | root label head tail => exact .skip label head (Select.refl tail)
  | head label tail _ ih => exact .keep ih (Select.refl tail)
  | tail label head _ ih => exact .keep (Select.refl head) ih

theorem Prunes.select {α : Type*} {small large : Word α} (h : Prunes small large) : Select small large := by
  induction h with
  | refl => exact Select.refl _
  | tail _ step ih => exact step.select.trans ih

theorem prunes_iff_select {α : Type*} (small large : Word α) : Prunes small large ↔ Select small large :=
  ⟨Prunes.select,Select.prunes⟩

def vertices {α : Type*} : Word α → List α
  | .nil => []
  | .node label head tail => label :: (vertices head ++ vertices tail)

def roots {α : Type*} : Word α → List α
  | .nil => []
  | .node label _ tail => label :: roots tail

def parentEdges {α : Type*} : Word α → List (α × α)
  | .nil => []
  | .node label head tail => (roots head).map (fun child => (label,child)) ++ parentEdges head ++ parentEdges tail

theorem Select.vertices_sublist {α : Type*} {small large : Word α} (h : Select small large) :
    (vertices small).Sublist (vertices large) := by
  induction h with
  | nil => simp [vertices]
  | skip label head _ ih =>
    exact (ih.trans (List.sublist_append_right _ _)).cons _
  | keep _ _ ihHead ihTail => exact (ihHead.append ihTail).cons_cons _

theorem Select.roots_sublist {α : Type*} {small large : Word α} (h : Select small large) :
    (roots small).Sublist (roots large) := by
  induction h with
  | nil => simp [roots]
  | skip label head _ ih => exact ih.cons _
  | keep _ _ _ ihTail => exact ihTail.cons_cons _

theorem Select.parentEdges_subset {α : Type*} {small large : Word α} (h : Select small large) :
    ∀ edge ∈ parentEdges small, edge ∈ parentEdges large := by
  induction h with
  | nil => simp [parentEdges]
  | skip label head _ ih =>
    intro edge hm
    simp only [parentEdges,List.mem_append]
    exact Or.inr (ih edge hm)
  | keep hHead hTail ihHead ihTail =>
    intro edge hm
    simp only [parentEdges,List.mem_append] at hm ⊢
    rcases hm with (hm | hm) | hm
    · obtain ⟨child,hChild,rfl⟩ := List.mem_map.mp hm
      exact Or.inl (Or.inl (List.mem_map.mpr ⟨child,hHead.roots_sublist.subset hChild,rfl⟩))
    · exact Or.inl (Or.inr (ihHead edge hm))
    · exact Or.inr (ihTail edge hm)

def erase {α : Type*} : Word α → List OrderedTree
  | .nil => []
  | .node _ head tail => .node (erase head) :: erase tail

theorem Select.erase {α : Type*} {small large : Word α} (h : Select small large) :
    OrderedTree.ForestPrunes (erase small) (erase large) := by
  induction h with
  | nil => exact .nil _
  | skip label head _ ih => exact .skip _ ih
  | keep _ _ ihHead ihTail => exact .cons (.node ihHead) ihTail

/-- An implicit parent may move down to an actual vertex; suffix cuts keep
that parent and head cuts move to a child's parent region. -/
inductive Region {α : Type*} : Word α → Word α → Prop where
  | refl (word : Word α) : Region word word
  | head (label : α) (tail : Word α) {region head : Word α} : Region region head →
      Region region (.node label head tail)
  | tail (label : α) (head : Word α) {region tail : Word α} : Region region tail →
      Region region (.node label head tail)

def AnyPrunes {α : Type*} (small large : Word α) : Prop := ∃ region, Region region large ∧ Prunes small region

theorem Prunes.any {α : Type*} {small large : Word α} (h : Prunes small large) : AnyPrunes small large :=
  ⟨large,.refl large,h⟩

theorem AnyPrunes.head {α : Type*} {small head : Word α} (h : AnyPrunes small head)
    (label : α) (tail : Word α) : AnyPrunes small (.node label head tail) := by
  obtain ⟨region,hRegion,hPrunes⟩ := h
  exact ⟨region,.head label tail hRegion,hPrunes⟩

theorem AnyPrunes.tail {α : Type*} {small tail : Word α} (h : AnyPrunes small tail)
    (label : α) (head : Word α) : AnyPrunes small (.node label head tail) := by
  obtain ⟨region,hRegion,hPrunes⟩ := h
  exact ⟨region,.tail label head hRegion,hPrunes⟩

theorem AnyPrunes.first {α : Type*} {small head tail : Word α} {label : α}
    (h : AnyPrunes small (.node label head tail)) :
    Prunes small (.node label head tail) ∨ AnyPrunes small head ∨ AnyPrunes small tail := by
  obtain ⟨region,hRegion,hPrunes⟩ := h
  cases hRegion with
  | refl => exact Or.inl hPrunes
  | head _ _ hRegion => exact Or.inr (Or.inl ⟨region,hRegion,hPrunes⟩)
  | tail _ _ hRegion => exact Or.inr (Or.inr ⟨region,hRegion,hPrunes⟩)

theorem Select.eq_nil_of_nil {α : Type*} {small : Word α} (h : Select small .nil) : small = .nil := by
  cases h
  rfl

theorem Prunes.eq_nil_of_nil {α : Type*} {small : Word α} (h : Prunes small .nil) : small = .nil :=
  h.select.eq_nil_of_nil

theorem AnyPrunes.eq_nil_of_nil {α : Type*} {small : Word α} (h : AnyPrunes small .nil) : small = .nil := by
  obtain ⟨region,hRegion,hPrunes⟩ := h
  cases hRegion
  exact hPrunes.eq_nil_of_nil

theorem Prunes.first {α : Type*} {label first : α} {head tail firstHead firstTail : Word α}
    (h : Prunes (.node label head tail) (.node first firstHead firstTail)) :
    Prunes (.node label head tail) firstTail ∨
      label = first ∧ Prunes head firstHead ∧ Prunes tail firstTail := by
  cases h.select with
  | skip _ _ hTail => exact Or.inl hTail.prunes
  | keep hHead hTail => exact Or.inr ⟨rfl,hHead.prunes,hTail.prunes⟩

@[simp] theorem vertices_length {α : Type*} (word : Word α) : (vertices word).length = word.numNodes := by
  induction word with
  | nil => rfl
  | node label head tail ihHead ihTail =>
    simp only [vertices,List.length_cons,List.length_append,ihHead,ihTail,BinaryTree.numNodes]

theorem Region.vertices_sublist {α : Type*} {region source : Word α} (h : Region region source) :
    (vertices region).Sublist (vertices source) := by
  induction h with
  | refl => exact List.Sublist.refl _
  | head label tail _ ih => exact (ih.trans (List.sublist_append_left _ _)).cons _
  | tail label head _ ih => exact (ih.trans (List.sublist_append_right _ _)).cons _

theorem Region.parentEdges_subset {α : Type*} {region source : Word α} (h : Region region source) :
    ∀ edge ∈ parentEdges region, edge ∈ parentEdges source := by
  induction h with
  | refl => exact fun _ hm => hm
  | head label tail _ ih =>
    intro edge hm
    simp only [parentEdges,List.mem_append]
    exact Or.inl (Or.inr (ih edge hm))
  | tail label head _ ih =>
    intro edge hm
    simp only [parentEdges,List.mem_append]
    exact Or.inr (ih edge hm)

theorem Prunes.vertices_sublist {α : Type*} {small large : Word α} (h : Prunes small large) :
    (vertices small).Sublist (vertices large) := h.select.vertices_sublist

theorem AnyPrunes.vertices_sublist {α : Type*} {small large : Word α} (h : AnyPrunes small large) :
    (vertices small).Sublist (vertices large) := by
  obtain ⟨region,hRegion,hPrunes⟩ := h
  exact hPrunes.vertices_sublist.trans hRegion.vertices_sublist

theorem Prunes.numNodes_le {α : Type*} {small large : Word α} (h : Prunes small large) :
    small.numNodes ≤ large.numNodes := by simpa using h.vertices_sublist.length_le

theorem AnyPrunes.numNodes_le {α : Type*} {small large : Word α} (h : AnyPrunes small large) :
    small.numNodes ≤ large.numNodes := by simpa using h.vertices_sublist.length_le

theorem Prunes.parentEdges_subset {α : Type*} {small large : Word α} (h : Prunes small large) :
    ∀ edge ∈ parentEdges small, edge ∈ parentEdges large := h.select.parentEdges_subset

theorem AnyPrunes.parentEdges_subset {α : Type*} {small large : Word α} (h : AnyPrunes small large) :
    ∀ edge ∈ parentEdges small, edge ∈ parentEdges large := by
  obtain ⟨region,hRegion,hPrunes⟩ := h
  exact fun edge hm => hRegion.parentEdges_subset edge (hPrunes.parentEdges_subset edge hm)

theorem Region.erase_prunes {α : Type*} {region source : Word α} (h : Region region source)
    (selected : List OrderedTree) (hPrunes : OrderedTree.ForestPrunes selected (erase region)) :
    OrderedTree.IsomorphicSubtree (.node selected) (.node (erase source)) := by
  induction h with
  | refl => exact (OrderedTree.RootPrunes.node hPrunes).isomorphicSubtree
  | head label tail _ ih => exact (ih hPrunes).below (by simp [erase,OrderedTree.children])
  | tail label head _ ih => exact (ih hPrunes).skip

theorem AnyPrunes.erase {α : Type*} {small large : Word α} (h : AnyPrunes small large) :
    OrderedTree.IsomorphicSubtree (.node (erase small)) (.node (erase large)) := by
  obtain ⟨region,hRegion,hPrunes⟩ := h
  exact hRegion.erase_prunes _ hPrunes.select.erase

end SubtreeProofs.Paper2004.AnnotatedIso

end
