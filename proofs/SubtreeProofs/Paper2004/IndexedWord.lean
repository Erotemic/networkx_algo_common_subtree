module

public import SubtreeProofs.Paper2004.DynamicProgram
import Mathlib.Tactic

/-!
# Independent indexed balanced-word deletion witnesses

Mathlib binary trees annotate matched pairs with their original input index.
The labels are retained identities, not matching scores. A single operation
deletes an enclosing pair at any structural context, splicing its interior
before its suffix. This operational relation is independent of the indexed
reconstruction algorithm and its Rust representation. Erasure refines the
existing independent Dyck/tree contraction semantics, while retained indices
form an ordered sublist of the original indices.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.IndexedWord

open OrderedTree

abbrev Word := BinaryTree Nat

/-- Forget pair identities, keeping precisely the balanced nesting. -/
def erase : Word → DyckWord
  | .nil => 0
  | .node _ head tail => (erase head).nest + erase tail

/-- Input pair identities in opening/preorder order. -/
def indices : Word → List Nat
  | .nil => []
  | .node index head tail => index::(indices head ++ indices tail)

/-- Ordered forest concatenation, retaining every original identity. -/
def append : Word → Word → Word
  | .nil,right => right
  | .node index head tail,right => .node index head (append tail right)

@[simp] theorem erase_append (left right : Word) : erase (append left right) = erase left + erase right := by
  induction left with
  | nil => simp [append,erase]
  | node index head tail _ ih => simp only [append,erase,ih,add_assoc]

@[simp] theorem indices_append (left right : Word) : indices (append left right) = indices left ++ indices right := by
  induction left with
  | nil => rfl
  | node index head tail _ ih => simp only [append,indices,ih,List.cons_append,List.append_assoc]

@[simp] theorem erase_semilength (word : Word) : (erase word).semilength = word.numNodes := by
  induction word with
  | nil => rfl
  | node index head tail ihHead ihTail =>
    simp only [erase,DyckWord.semilength_add,DyckWord.semilength_nest,ihHead,ihTail,BinaryTree.numNodes]
    omega

@[simp] theorem indices_length (word : Word) : (indices word).length = word.numNodes := by
  induction word with
  | nil => rfl
  | node index head tail ihHead ihTail =>
    simp only [indices,List.length_cons,List.length_append,ihHead,ihTail,BinaryTree.numNodes]

/-- A structural hole can occur inside a pair or among its following siblings. -/
inductive Context where
  | hole : Context
  | head (index : Nat) (inner : Context) (suffix : Word) : Context
  | tail (index : Nat) (interior : Word) (inner : Context) : Context

namespace Context

def plug : Context → Word → Word
  | .hole,word => word
  | .head index inner suffix,word => .node index (plug inner word) suffix
  | .tail index interior inner,word => .node index interior (plug inner word)

def compose : Context → Context → Context
  | .hole,inner => inner
  | .head index outer suffix,inner => .head index (compose outer inner) suffix
  | .tail index interior outer,inner => .tail index interior (compose outer inner)

theorem plug_compose (outer inner : Context) (word : Word) :
    (outer.compose inner).plug word = outer.plug (inner.plug word) := by
  induction outer with
  | hole => rfl
  | head index outer suffix ih => simp only [compose,plug,ih]
  | tail index interior outer ih => simp only [compose,plug,ih]

theorem indices_mono (context : Context) {small large : Word} (h : (indices small).Sublist (indices large)) :
    (indices (context.plug small)).Sublist (indices (context.plug large)) := by
  induction context with
  | hole => exact h
  | head index inner suffix ih =>
    exact (ih.append_right (indices suffix)).cons_cons index
  | tail index interior inner ih =>
    exact (ih.append_left (indices interior)).cons_cons index

theorem erase_mono (context : Context) {small large : Word} (h : DyckEmbeds (erase small) (erase large)) :
    DyckEmbeds (erase (context.plug small)) (erase (context.plug large)) := by
  induction context with
  | hole => exact h
  | head index inner suffix ih =>
    exact dyckEmbeds_add (dyckEmbeds_context (.nested .hole) ih) Relation.ReflTransGen.refl
  | tail index interior inner ih =>
    exact dyckEmbeds_add Relation.ReflTransGen.refl ih

end Context

/-- Delete an actual matched pair, retaining its indexed interior and suffix. -/
def Step (before after : Word) : Prop :=
  ∃ (context : Context) (index : Nat) (head tail : Word), before = context.plug (.node index head tail) ∧ after = context.plug (append head tail)

/-- Indexed operational containment, defined without any solver or erasure. -/
def Retains (small large : Word) : Prop := Relation.ReflTransGen Step large small

theorem Step.root (index : Nat) (head tail : Word) : Step (.node index head tail) (append head tail) :=
  ⟨.hole,index,head,tail,rfl,rfl⟩

theorem Step.context (context : Context) {before after : Word} (h : Step before after) :
    Step (context.plug before) (context.plug after) := by
  obtain ⟨inner,index,head,tail,hb,ha⟩ := h
  refine ⟨context.compose inner,index,head,tail,?_,?_⟩
  · rw [Context.plug_compose,hb]
  · rw [Context.plug_compose,ha]

theorem Retains.context (context : Context) {small large : Word} (h : Retains small large) :
    Retains (context.plug small) (context.plug large) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (hstep.context context)

theorem Retains.trans {small middle large : Word} (hsmall : Retains small middle) (hlarge : Retains middle large) :
    Retains small large := Relation.ReflTransGen.trans hlarge hsmall

/-- Retaining a pair combines independent interior and suffix deletions while
keeping the pair's exact original identity. -/
theorem Retains.keep (index : Nat) {smallHead largeHead smallTail largeTail : Word}
    (hh : Retains smallHead largeHead) (ht : Retains smallTail largeTail) :
    Retains (.node index smallHead smallTail) (.node index largeHead largeTail) := by
  exact (ht.context (.tail index smallHead .hole)).trans (hh.context (.head index .hole largeTail))

theorem empty_retains (word : Word) : Retains .nil word := by
  induction word with
  | nil => exact Relation.ReflTransGen.refl
  | node index head tail ihHead ihTail =>
    exact Retains.trans (Relation.ReflTransGen.single (Step.root index .nil .nil)) (Retains.keep index ihHead ihTail)

/-- Indexed deletion never reorders, duplicates or invents an input identity. -/
theorem Step.indices_sublist {before after : Word} (h : Step before after) : (indices after).Sublist (indices before) := by
  obtain ⟨context,index,head,tail,hb,ha⟩ := h
  rw [hb,ha]
  apply Context.indices_mono
  rw [indices_append]
  exact List.sublist_cons_self index (indices head ++ indices tail)

theorem Retains.indices_sublist {small large : Word} (h : Retains small large) : (indices small).Sublist (indices large) := by
  induction h with
  | refl => exact List.Sublist.refl _
  | tail _ hstep ih => exact hstep.indices_sublist.trans ih

/-- Distinct original pair indices remain distinct in the returned witness. -/
theorem Retains.indices_nodup {small large : Word} (h : Retains small large) (hd : (indices large).Nodup) :
    (indices small).Nodup := h.indices_sublist.nodup hd

/-- Every retained identity is a genuine original index under canonical
zero-based numbering. The bound follows from the deletion relation itself. -/
theorem Retains.index_lt {small large : Word} (h : Retains small large) (count : Nat)
    (hnumbered : indices large = List.range count) (index : Nat) (hi : index ∈ indices small) : index < count := by
  have hm := h.indices_sublist.subset hi
  simpa only [hnumbered,List.mem_range] using hm

/-- Erasing retained indices gives a genuine independent operational embedding. -/
theorem Step.erase_embeds {before after : Word} (h : Step before after) : DyckEmbeds (erase after) (erase before) := by
  obtain ⟨context,index,head,tail,hb,ha⟩ := h
  rw [hb,ha]
  apply Context.erase_mono
  simpa only [erase,erase_append,zero_add] using dyckEmbeds_remove 0 (erase head) (erase tail)

theorem Retains.erase_embeds {small large : Word} (h : Retains small large) : DyckEmbeds (erase small) (erase large) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact dyckEmbeds_trans hstep.erase_embeds ih

/-- The indexed witness decodes to the independently specified contracted tree. -/
theorem Retains.tree_embedding {small large : Word} (h : Retains small large) :
    Embeds (decodeDyck (erase small)) (decodeDyck (erase large)) :=
  dyckEmbeds_decodeDyck h.erase_embeds

end SubtreeProofs.Paper2004.IndexedWord

end
