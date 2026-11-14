module

public import SubtreeProofs.Rust.MatchingCostConstruction
import Mathlib.Tactic

/-!
# Actual indexed-pair decoding for partial matching

The independent coordinate predicate keeps exactly positive compatible
real-left/real-right assignments. The actual helper and complete owned-vector
loop safely return that finite indexed list, in increasing left-row order.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingDecoding

open MatchingCostSpecification MatchingCostConstruction

def pairValue (pair : matching.MatchedPair) : Nat × Nat := (pair.left.val,pair.right.val)

def decodedAt (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat) (columns : Slice Usize) (row : Nat) : Option (Nat × Nat) :=
  let col := columns.val[row]!.val
  if left ≤ col ∧ col-left < right ∧ 0 < ((weightValue (weights.val[row]!).val[col-left]!).getD 0)
  then some (row,col-left) else none

/-- The actual helper is safe and returns exactly the independent positive
compatible coordinate predicate, even for ignored dummy/outside columns. -/
theorem decode_pair_spec (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension : Usize)
    (columns : Slice Usize) (row : Usize) (dims : Dimensions weights left right dimension)
    (hr : row.val < left.val) (hcolumns : left.val ≤ columns.length) :
    matching.decode_pair weights left right columns row ⦃ result =>
      result.map pairValue = decodedAt weights left.val right.val columns row.val ⦄ := by
  have hb : row.val < columns.length := lt_of_lt_of_le hr hcolumns
  unfold matching.decode_pair
  apply WP.spec_bind (Slice.index_usize_spec columns row hb)
  intro column hColumn
  have hcolumn : column = columns.val[row.val]! := by
    simpa only [getElem!_pos columns.val row.val hb] using hColumn
  have hcv : column.val = columns.val[row.val]!.val := congrArg UScalar.val hcolumn
  split
  · rename_i hc
    have hleft : left.val ≤ columns.val[row.val]!.val := by scalar_tac
    apply WP.spec_bind (Usize.sub_spec (x := column) (y := left) (by scalar_tac))
    intro target hTarget
    have ht : target.val = columns.val[row.val]!.val-left.val := by scalar_tac
    split
    · rename_i hright
      have hrightVal : columns.val[row.val]!.val-left.val < right.val := by scalar_tac
      have hw : row.val < weights.length := by rw [dims.left_len]; exact hr
      apply WP.spec_bind (Slice.index_usize_spec weights row hw)
      intro inputRow hInputRow
      have hrow : inputRow = weights.val[row.val]! := by
        simpa only [getElem!_pos weights.val row.val hw] using hInputRow
      have htarget : target.val < inputRow.length := by
        rw [hrow,dims.row_length weights left right dimension row.val hr]
        scalar_tac
      simp only [alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec inputRow target htarget)
      intro entry hEntry
      have he : entry = (weights.val[row.val]!).val[columns.val[row.val]!.val-left.val]! := by
        have he' : entry = inputRow.val[target.val]! := by
          simpa only [getElem!_pos inputRow.val target.val htarget] using hEntry
        simpa only [hrow,ht] using he'
      rw [he]
      cases hweight : (weights.val[row.val]!).val[columns.val[row.val]!.val-left.val]! with
      | none =>
        simp only [WP.spec_ok,Option.map_none,decodedAt,hleft,hrightVal,weightValue,hweight,Option.getD_none,
          lt_irrefl,and_false,↓reduceIte]
      | some weight =>
        simp only
        split
        · rename_i hp
          have hpositive : 0 < weight.val := by scalar_tac
          simp only [WP.spec_ok,Option.map_some,pairValue,decodedAt,hleft,hrightVal,weightValue,hweight,
            Option.getD_some,hpositive,and_self,↓reduceIte,ht]
        · rename_i hp
          have hnonpositive : ¬ 0 < weight.val := by scalar_tac
          simp only [WP.spec_ok,Option.map_none,decodedAt,hleft,hrightVal,weightValue,hweight,
            Option.getD_some,hnonpositive,and_false,↓reduceIte]
    · rename_i hright
      have hn : ¬ columns.val[row.val]!.val-left.val < right.val := by scalar_tac
      simp only [WP.spec_ok,Option.map_none,decodedAt,hn,false_and,and_false,↓reduceIte]
  · rename_i hc
    have hn : ¬ left.val ≤ columns.val[row.val]!.val := by scalar_tac
    simp only [WP.spec_ok,Option.map_none,decodedAt,hn,false_and,↓reduceIte]

def decodedPrefix (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat) (columns : Slice Usize) (count : Nat) : List (Nat × Nat) :=
  (List.range count).filterMap (decodedAt weights left right columns)

theorem decodedPrefix_length_le (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat)
    (columns : Slice Usize) (count : Nat) : (decodedPrefix weights left right columns count).length ≤ count := by
  simpa only [decodedPrefix,List.length_range] using List.length_filterMap_le (decodedAt weights left right columns) (List.range count)

theorem decodedPrefix_succ (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat) (columns : Slice Usize) (count : Nat) :
    decodedPrefix weights left right columns (count+1) = decodedPrefix weights left right columns count ++
      (decodedAt weights left right columns count).toList := by
  simp only [decodedPrefix,List.range_succ,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Option.toList]
  rfl

/-- The actual complete decoder safely returns exactly the finite indexed
witness list selected by the independent positive compatible predicate. -/
theorem decode_pairs_spec (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension : Usize)
    (columns : Slice Usize) (dims : Dimensions weights left right dimension) (hcolumns : left.val ≤ columns.length) :
    matching.decode_pairs weights left right columns ⦃ result =>
      result.val.map pairValue = decodedPrefix weights left.val right.val columns left.val ⦄ := by
  unfold matching.decode_pairs matching.decode_pairs_loop
  apply loop.spec_decr_nat (fun (state : alloc.vec.Vec matching.MatchedPair × Usize) => left.val-state.2.val)
    (fun (state : alloc.vec.Vec matching.MatchedPair × Usize) => state.2.val ≤ left.val ∧
      state.1.val.map pairValue = decodedPrefix weights left.val right.val columns state.2.val)
    (fun (result : alloc.vec.Vec matching.MatchedPair) => result.val.map pairValue = decodedPrefix weights left.val right.val columns left.val)
    _ _ ?_ (by simp [decodedPrefix])
  rintro ⟨pairs,row⟩ ⟨hrow,hprefix⟩
  dsimp only at hrow hprefix ⊢
  unfold matching.decode_pairs_loop.body
  split
  · rename_i hr
    have hi : row.val < left.val := by scalar_tac
    have hlen : pairs.val.length ≤ row.val := by
      have he := congrArg List.length hprefix
      have hb := decodedPrefix_length_le weights left.val right.val columns row.val
      simpa only [List.length_map] using he.le.trans hb
    apply WP.spec_bind (decode_pair_spec weights left right dimension columns row dims hi hcolumns)
    intro entry hEntry
    cases entry with
    | none =>
      simp only [Option.map_none] at hEntry
      simp only [bind_ok]
      apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
      intro next hNext
      have hnext : next.val = row.val+1 := by simpa using hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by omega,?_⟩,by omega⟩
      rw [hnext,decodedPrefix_succ,← hEntry,Option.toList_none,List.append_nil]
      exact hprefix
    | some pair =>
      simp only [Option.map_some] at hEntry
      apply WP.spec_bind (alloc.vec.Vec.push_spec pairs pair (by scalar_tac))
      intro newPairs hNewPairs
      apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
      intro next hNext
      have hnext : next.val = row.val+1 := by simpa using hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by omega,?_⟩,by omega⟩
      rw [hNewPairs,List.map_append,List.map_cons,List.map_nil,hprefix,hnext,decodedPrefix_succ,← hEntry,Option.toList_some]
  · rename_i hr
    have he : row.val = left.val := by scalar_tac
    simp only [WP.spec_ok]
    simpa only [he] using hprefix

end SubtreeProofs.Rust.MatchingDecoding

end
