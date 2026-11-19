module

public import SubtreeProofs.Shared.AssignmentRankedAugmentation
import Mathlib.Tactic

/-! # Prefix writes of the canonical predecessor-path augmentation -/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A B : Type*} [DecidableEq A]

def traceRows (predecessor : A → A) (path : List A) (cursor : Nat) : Finset A :=
  (path.take cursor).toFinset.image predecessor

@[simp] theorem traceRows_zero (predecessor : A → A) (path : List A) : traceRows predecessor path 0 = ∅ := by
  simp only [traceRows,List.take_zero,List.toFinset_nil,Finset.image_empty]

theorem traceRows_succ (predecessor : A → A) (path : List A) (cursor : Nat) (hc : cursor < path.length) :
    traceRows predecessor path (cursor+1) = insert (predecessor path[cursor]) (traceRows predecessor path cursor) := by
  simp only [traceRows,List.take_succ_eq_append_getElem hc,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
    Finset.image_union,Finset.image_insert,Finset.image_empty,LawfulSingleton.insert_empty_eq,Finset.union_singleton]

def tracePrefixValue (before after : A → B) (predecessor : A → A) (path : List A) (cursor : Nat) (row : A) : B :=
  if row ∈ traceRows predecessor path cursor then after row else before row

@[simp] theorem tracePrefixValue_zero (before after : A → B) (predecessor : A → A) (path : List A) (row : A) :
    tracePrefixValue before after predecessor path 0 row = before row := by
  simp only [tracePrefixValue,traceRows_zero,Finset.notMem_empty,↓reduceIte]

/-- One original-coordinate overwrite records the final value of precisely
the next predecessor row and preserves every other prefix coordinate. -/
theorem tracePrefixValue_succ (before after : A → B) (predecessor : A → A) (path : List A)
    (cursor : Nat) (hc : cursor < path.length) (row : A) :
    tracePrefixValue before after predecessor path (cursor+1) row =
      if row = predecessor path[cursor] then after row else tracePrefixValue before after predecessor path cursor row := by
  unfold tracePrefixValue
  simp only [traceRows_succ predecessor path cursor hc,Finset.mem_insert]
  by_cases he : row = predecessor path[cursor] <;> simp only [he,↓reduceIte,true_or,false_or]

/-- Once every trace predecessor is written, untouched rows already have
their final value because the augmentation fixes all other old assignments. -/
theorem tracePrefixValue_final (assignment : Equiv.Perm A) (predecessor : A → A) (root : A) (rest : List A)
    (ht : PredecessorTrace assignment predecessor root (assignment root) (assignment root::rest))
    (hn : (assignment root::rest).Nodup) (row : A) :
    tracePrefixValue assignment (augmentTrace assignment (assignment root::rest)) predecessor (assignment root::rest)
      (assignment root::rest).length row = augmentTrace assignment (assignment root::rest) row := by
  unfold tracePrefixValue
  split
  · rfl
  · rename_i hOutside
    apply (augmentTrace_away assignment (assignment root::rest) row ?_).symm
    intro hm
    have he : predecessor (augmentTrace assignment (assignment root::rest) row) = row :=
      (augmentTrace assignment (assignment root::rest)).injective
        (augmentTrace_predecessor assignment predecessor root rest ht hn _ hm)
    apply hOutside
    apply Finset.mem_image.mpr
    refine ⟨augmentTrace assignment (assignment root::rest) row,?_,he⟩
    simpa only [List.take_length,List.mem_toFinset] using hm

end SubtreeProofs.Assignment

end
