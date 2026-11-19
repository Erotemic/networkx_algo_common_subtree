module

public import SubtreeProofs.Rust.Generated.VerifiedOrderedCore
public import Mathlib.Data.Tree.Basic
import Mathlib.Tactic

/-! # Independent forest interpretation of production isomorphism choices

Arena coordinates are original token pairs, not scores. Child indices refer
to earlier entries. The tree interpretation is well founded on the arena
index, independently of the source's explicit work stack.
-/

@[expose] public section

open Aeneas Aeneas.Std
open verified_ordered_core.isomorphism_choices

namespace SubtreeProofs.Rust.IsomorphismChoices

abbrev ChoiceTree := BinaryTree ((U32 × U32) × (U32 × U32))

def ValidArena (choices : Slice IsomorphismChoice) : Prop :=
  ∀ index (hi : index < choices.length),
    (∀ child, choices.val[index].head = some child → child.val < index) ∧
    (∀ child, choices.val[index].tail = some child → child.val < index)

/-- Interpret a stored choice as a forest, with explicit open/close token
coordinates in both original inputs. Invalid references denote an empty
forest here; source correctness is stated for valid roots/arenas. -/
def treeAt (choices : Slice IsomorphismChoice) (index : Nat) : ChoiceTree :=
  if hi : index < choices.length then
    let choice := choices.val[index]
    .node ((choice.left_open,choice.right_open),(choice.left_close,choice.right_close))
      (match choice.head with
        | none => .nil
        | some child => if child.val < index then treeAt choices child.val else .nil)
      (match choice.tail with
        | none => .nil
        | some child => if child.val < index then treeAt choices child.val else .nil)
  else .nil
termination_by index

def optionalTree (choices : Slice IsomorphismChoice) : Option Usize → ChoiceTree
  | none => .nil
  | some index => treeAt choices index.val

def tokens : ChoiceTree → List (U32 × U32)
  | .nil => []
  | .node ends head tail => ends.1 :: (tokens head ++ ends.2 :: tokens tail)

@[simp] theorem tokens_length (word : ChoiceTree) : (tokens word).length = 2*word.numNodes := by
  induction word with
  | nil => rfl
  | node ends head tail ihHead ihTail =>
    simp only [tokens,List.length_cons,List.length_append,ihHead,ihTail,BinaryTree.numNodes]
    omega

theorem treeAt_eq (choices : Slice IsomorphismChoice) (index : Nat)
    (hValid : ValidArena choices) (hi : index < choices.length) :
    treeAt choices index =
      .node ((choices.val[index].left_open,choices.val[index].right_open),
        (choices.val[index].left_close,choices.val[index].right_close))
        (optionalTree choices choices.val[index].head) (optionalTree choices choices.val[index].tail) := by
  rw [treeAt]
  simp only [dite_eq_left hi]
  congr 1
  · cases hh : choices.val[index].head with
    | none => rfl
    | some child => simp only [(hValid index hi).1 child hh,↓reduceIte,optionalTree]
  · cases ht : choices.val[index].tail with
    | none => rfl
    | some child => simp only [(hValid index hi).2 child ht,↓reduceIte,optionalTree]

def ValidVisit (choices : Slice IsomorphismChoice) : Visit → Prop
  | .Pair index => index.val < choices.length
  | .Close _ _ => True

def visitTokens (choices : Slice IsomorphismChoice) : Visit → List (U32 × U32)
  | .Pair index => tokens (treeAt choices index.val)
  | .Close left right => [(left,right)]

def ValidStack (choices : Slice IsomorphismChoice) (pending : List Visit) : Prop :=
  ∀ visit ∈ pending, ValidVisit choices visit

/-- The last stored task runs first. This is the remaining ordered output,
not a restatement of the imperative stack loop. -/
def stackTokens (choices : Slice IsomorphismChoice) (pending : List Visit) : List (U32 × U32) :=
  pending.reverse.flatMap (visitTokens choices)

@[simp] theorem stackTokens_nil (choices : Slice IsomorphismChoice) : stackTokens choices [] = [] := rfl

theorem stackTokens_append (choices : Slice IsomorphismChoice) (pending : List Visit) (visit : Visit) :
    stackTokens choices (pending ++ [visit]) = visitTokens choices visit ++ stackTokens choices pending := by
  simp [stackTokens,List.reverse_append]

theorem visit_tokens_nonempty (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (visit : Visit) (hv : ValidVisit choices visit) : 1 ≤ (visitTokens choices visit).length := by
  cases visit with
  | Pair index =>
    rw [visitTokens,treeAt_eq choices index.val hValid hv]
    simp only [tokens,List.length_cons,List.length_append]
    omega
  | Close left right => simp [visitTokens]

/-- A task uses at least one future token, bounding live stack slots by the
remaining output. This supports actual checked vector pushes without a
capacity oracle or a recursive-call-count assumption. -/
theorem stack_length_bound (choices : Slice IsomorphismChoice) (hValid : ValidArena choices)
    (pending : List Visit) (hs : ValidStack choices pending) :
    pending.length ≤ (stackTokens choices pending).length := by
  induction pending with
  | nil => simp
  | cons visit rest ih =>
    have hv := visit_tokens_nonempty choices hValid visit (hs visit (by simp))
    have hr := ih (fun value hm => hs value (by simp [hm]))
    simp only [stackTokens,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append] at *
    simp only [List.length_cons]
    omega

end SubtreeProofs.Rust.IsomorphismChoices

end
