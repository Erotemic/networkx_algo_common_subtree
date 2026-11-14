module

public import SubtreeProofs.Paper2004.TokenEncoding
import Mathlib.Tactic

/-! # Canonical original pair coordinates enumerate exactly the original token array -/

@[expose] public section

namespace SubtreeProofs.Paper2004.TokenEncoding

open IndexedWord

/-- Expanding canonical indexed pairs through the exact original coordinate
table returns every original token position in order, including both endpoints.
Arbitrary leading/trailing records make the induction apply to interior and
suffix tables without changing their global pair identities. -/
theorem canonical_tokenIndices (shape : BinaryTree Unit) (start : Nat) (leading trailing : List (Nat × Nat)) :
    tokenIndices (fun index => (leading ++ positionPairs shape start ++ trailing)[index]!)
      (numberFrom shape leading.length) = List.range' start (2*shape.numNodes) := by
  induction shape generalizing start leading trailing with
  | nil => rfl
  | node value head tail ihHead ihTail =>
    let root : Nat × Nat := (start,start+2*head.numNodes+1)
    have hh := ihHead (start+1) (leading++[root]) (positionPairs tail (start+2*head.numNodes+2)++trailing)
    have ht := ihTail (start+2*head.numNodes+2) (leading++root::positionPairs head (start+1)) trailing
    have htailIndex : (leading++root::positionPairs head (start+1)).length = leading.length+1+head.numNodes := by
      simp only [List.length_append,List.length_cons,positionPairs_length]
      omega
    rw [htailIndex] at ht
    simp only [List.length_append,List.length_singleton,List.append_assoc,List.cons_append,List.nil_append] at hh
    simp only [List.append_assoc,List.cons_append] at ht
    have hroot : (leading ++ positionPairs (.node value head tail) start ++ trailing)[leading.length]! = root := by
      have hb : leading.length < (leading ++ positionPairs (.node value head tail) start ++ trailing).length := by
        simp only [List.length_append,positionPairs_length,BinaryTree.numNodes]
        omega
      rw [getElem!_pos (leading ++ positionPairs (.node value head tail) start ++ trailing) leading.length hb]
      exact List.getElem_of_append (l₁ := leading)
        (l₂ := positionPairs head (start+1) ++ positionPairs tail (start+2*head.numNodes+2) ++ trailing)
        (a := root) (by simp only [positionPairs,root,List.append_assoc,List.cons_append]) rfl
    simp only [numberFrom,tokenIndices]
    rw [hroot]
    simp only [positionPairs,List.append_assoc,List.cons_append]
    rw [hh,ht]
    change start :: (List.range' (start+1) (2*head.numNodes) ++
      (start+2*head.numNodes+1) :: List.range' (start+2*head.numNodes+2) (2*tail.numNodes)) = _
    have hc : start+2*head.numNodes+1 = (start+1)+2*head.numNodes := by omega
    have htstart : start+2*head.numNodes+2 = ((start+1)+2*head.numNodes)+1 := by omega
    rw [hc,htstart,← List.range'_succ,List.range'_append_1,← List.range'_succ]
    simp only [BinaryTree.numNodes]
    congr 1
    omega

/-- The public parser's empty-prefix original table expands to exactly the
zero-based token array; no arbitrary coordinate-validity premise is needed. -/
theorem canonical_tokenIndices_zero (shape : BinaryTree Unit) :
    tokenIndices (fun index => (positionPairs shape 0)[index]!) (numberFrom shape 0) = List.range (2*shape.numNodes) := by
  have h := canonical_tokenIndices shape 0 [] []
  simpa only [List.nil_append,List.append_nil,List.length_nil,List.range_eq_range'] using h

end SubtreeProofs.Paper2004.TokenEncoding

end
