module

public import SubtreeProofs.Paper2004.CanonicalIndexedWord
import Mathlib.Tactic

/-!
# Retained original opening and closing token positions

A pair-position map gives both original token coordinates for each original
pair identity. Reading a retained indexed word emits the opening coordinate,
its interior, the closing coordinate, and its suffix. Operational pair deletion
preserves an ordered sublist of these exact token coordinates. Thus a valid
original coordinate range supplies uniqueness and bounds to every retained
witness without postulating an index-map correctness certificate.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.IndexedWord

/-- Both original token positions of a surviving pair, emitted in nesting order. -/
def tokenIndices (positions : Nat → Nat × Nat) : Word → List Nat
  | .nil => []
  | .node index head tail => (positions index).1 ::
      (tokenIndices positions head ++ (positions index).2 :: tokenIndices positions tail)

@[simp] theorem tokenIndices_append (positions : Nat → Nat × Nat) (left right : Word) :
    tokenIndices positions (append left right) = tokenIndices positions left ++ tokenIndices positions right := by
  induction left with
  | nil => rfl
  | node index head tail _ ih => simp only [append,tokenIndices,ih,List.cons_append,List.append_assoc]

@[simp] theorem tokenIndices_length (positions : Nat → Nat × Nat) (word : Word) :
    (tokenIndices positions word).length = 2*word.numNodes := by
  induction word with
  | nil => rfl
  | node index head tail ihHead ihTail =>
    simp only [tokenIndices,List.length_cons,List.length_append,ihHead,ihTail,BinaryTree.numNodes]
    omega

/-- Replacing a context hole by an ordered coordinate sublist preserves the
same relation for the whole indexed original, including both enclosing tokens. -/
theorem Context.tokenIndices_mono (positions : Nat → Nat × Nat) (context : Context) {small large : Word}
    (h : (tokenIndices positions small).Sublist (tokenIndices positions large)) :
    (tokenIndices positions (context.plug small)).Sublist (tokenIndices positions (context.plug large)) := by
  induction context with
  | hole => exact h
  | head index inner suffix ih =>
    exact (ih.append_right ((positions index).2 :: tokenIndices positions suffix)).cons_cons (positions index).1
  | tail index interior inner ih =>
    exact ((ih.cons_cons (positions index).2).append_left (tokenIndices positions interior)).cons_cons (positions index).1

/-- One actual pair deletion removes its exact opening and closing coordinates,
retaining every other coordinate in source order. -/
theorem Step.tokenIndices_sublist (positions : Nat → Nat × Nat) {before after : Word} (h : Step before after) :
    (tokenIndices positions after).Sublist (tokenIndices positions before) := by
  obtain ⟨context,index,head,tail,hb,ha⟩ := h
  rw [hb,ha]
  apply Context.tokenIndices_mono
  rw [tokenIndices_append]
  exact ((List.Sublist.refl (tokenIndices positions head)).append
    (List.sublist_cons_self (positions index).2 (tokenIndices positions tail))).cons (positions index).1

theorem Retains.tokenIndices_sublist (positions : Nat → Nat × Nat) {small large : Word} (h : Retains small large) :
    (tokenIndices positions small).Sublist (tokenIndices positions large) := by
  induction h with
  | refl => exact List.Sublist.refl _
  | tail _ hstep ih => exact (hstep.tokenIndices_sublist positions).trans ih

/-- Token identities remain distinct whenever the original coordinate stream
was distinct, not merely after conversion to a finite set. -/
theorem Retains.tokenIndices_nodup (positions : Nat → Nat × Nat) {small large : Word} (h : Retains small large)
    (hd : (tokenIndices positions large).Nodup) : (tokenIndices positions small).Nodup :=
  (h.tokenIndices_sublist positions).nodup hd

/-- Every retained token position is in the original actual token array. -/
theorem Retains.tokenIndex_lt (positions : Nat → Nat × Nat) {small large : Word} (h : Retains small large)
    (count : Nat) (hpositions : tokenIndices positions large = List.range count)
    (index : Nat) (hi : index ∈ tokenIndices positions small) : index < count := by
  have hm := (h.tokenIndices_sublist positions).subset hi
  simpa only [hpositions,List.mem_range] using hm

end SubtreeProofs.Paper2004.IndexedWord

end
