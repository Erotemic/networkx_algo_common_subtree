module

public import SubtreeProofs.Paper2004.IndexedTokenPositions
import Mathlib.Tactic

/-! # Independent flat Boolean encoding and original pair token coordinates -/

@[expose] public section

namespace SubtreeProofs.Paper2004.TokenEncoding

/-- The core's typed alphabet: false opens a pair; true closes it. -/
def encodeStep : DyckStep → Bool
  | .U => false
  | .D => true

def decodeStep : Bool → DyckStep
  | false => .U
  | true => .D

@[simp] theorem decode_encodeStep (step : DyckStep) : decodeStep (encodeStep step) = step := by cases step <;> rfl

/-- Independent encoding of the established mathematical Dyck language. -/
def encoded (word : DyckWord) : List Bool := word.toList.map encodeStep

@[simp] theorem encoded_zero : encoded 0 = [] := rfl

@[simp] theorem encoded_nest_add (head tail : DyckWord) :
    encoded (head.nest+tail) = false :: (encoded head ++ true :: encoded tail) := by
  change (([DyckStep.U] ++ head.toList ++ [DyckStep.D]) ++ tail.toList).map encodeStep = _
  simp only [List.map_append,List.map_cons,List.map_nil,encodeStep,List.singleton_append,List.nil_append,List.append_assoc]
  rfl

@[simp] theorem encoded_length (word : DyckWord) : (encoded word).length = 2*word.semilength := by
  rw [encoded,List.length_map,word.two_mul_semilength_eq_length]

theorem encoded_injective : Function.Injective encoded := by
  intro first second he
  apply DyckWord.ext
  have hh := congrArg (List.map decodeStep) he
  simpa only [encoded,List.map_map,Function.comp_def,decode_encodeStep,List.map_id'] using hh

/-- Valid flat input, independently of any parser implementation. -/
def Balanced (tokens : List Bool) : Prop := ∃ word : DyckWord, tokens = encoded word

/-- Stop a forest at the end of input or immediately before a closing token. -/
def Stops (suffix : List Bool) : Prop := suffix = [] ∨ ∃ rest, suffix = true::rest

/-- Exact original opening/closing coordinates in preorder pair order. This
specification uses only the original independent binary shape and token offset. -/
def positionPairs : BinaryTree Unit → Nat → List (Nat × Nat)
  | .nil,_ => []
  | .node _ head tail,start =>
    (start,start+2*head.numNodes+1) ::
      (positionPairs head (start+1) ++ positionPairs tail (start+2*head.numNodes+2))

@[simp] theorem positionPairs_length (shape : BinaryTree Unit) (start : Nat) :
    (positionPairs shape start).length = shape.numNodes := by
  induction shape generalizing start with
  | nil => rfl
  | node _ head tail ihHead ihTail =>
    simp only [positionPairs,List.length_cons,List.length_append,ihHead,ihTail,BinaryTree.numNodes]

/-- Both recorded coordinates are genuine tokens inside the exact original
encoded segment, with the opening strictly before its matching closing token. -/
theorem positionPairs_bounds (shape : BinaryTree Unit) (start : Nat) (pair : Nat × Nat)
    (h : pair ∈ positionPairs shape start) :
    start ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 < start+2*shape.numNodes := by
  induction shape generalizing start with
  | nil => cases h
  | node _ head tail ihHead ihTail =>
    simp only [positionPairs,List.mem_cons,List.mem_append] at h
    simp only [BinaryTree.numNodes]
    rcases h with rfl | hhead | htail
    · dsimp only
      omega
    · have hh := ihHead (start+1) hhead
      omega
    · have ht := ihTail (start+2*head.numNodes+2) htail
      omega

/-- A coordinate is emitted exactly once per original pair record; the pair
record count is the independently established edge semilength. -/
theorem positionPairs_toTree_length (word : DyckWord) (start : Nat) :
    (positionPairs word.toTree start).length = word.semilength := by
  rw [positionPairs_length,DyckWord.numNodes_toTree]

end SubtreeProofs.Paper2004.TokenEncoding

end
