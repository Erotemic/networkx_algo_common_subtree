module

public import SubtreeProofs.Rust.IndexedWordRepresentation
public import SubtreeProofs.Paper2004.TokenEncoding
import Mathlib.Tactic

/-! # Actual parser coordinate vectors and independent flat-word representation -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenParser

open OrderedSolver IndexedOrderedSolver Paper2004.TokenEncoding

def wordTokens (word : BalancedWord) : List Bool := encoded (toDyck word)

@[simp] theorem wordTokens_empty : wordTokens .Empty = [] := rfl

@[simp] theorem wordTokens_pair (head tail : BalancedWord) :
    wordTokens (.Pair head tail) = false :: (wordTokens head ++ true :: wordTokens tail) :=
  encoded_nest_add (toDyck head) (toDyck tail)

@[simp] theorem wordTokens_length (word : BalancedWord) : (wordTokens word).length = 2*(toDyck word).semilength :=
  encoded_length (toDyck word)

def positionValue (position : tokens.PairPositions) : Nat × Nat := (position.«open».val,position.close.val)

def coordinateView (positions : alloc.vec.Vec tokens.PairPositions) : List (Nat × Nat) := positions.val.map positionValue

@[simp] theorem coordinateView_length (positions : alloc.vec.Vec tokens.PairPositions) :
    (coordinateView positions).length = positions.length := by simp only [coordinateView,List.length_map,alloc.vec.Vec.length]

/-- The actual source push appends precisely the specified machine coordinates. -/
theorem position_push_spec (positions : alloc.vec.Vec tokens.PairPositions) (position : tokens.PairPositions)
    (hb : positions.length < Usize.max) :
    alloc.vec.Vec.push positions position ⦃ result => coordinateView result = coordinateView positions ++ [positionValue position] ⦄ := by
  apply WP.spec_mono (alloc.vec.Vec.push_spec positions position hb)
  intro result hr
  simp only [coordinateView,hr,List.map_append,List.map_cons,List.map_nil]

/-- Bounded physical reads agree with the independent coordinate-list view. -/
theorem coordinateView_get (positions : alloc.vec.Vec tokens.PairPositions) (index : Usize) (hb : index.val < positions.length) :
    (coordinateView positions)[index.val]! = positionValue positions.val[index.val] := by
  rw [getElem!_pos (coordinateView positions) index.val (by simpa only [coordinateView_length] using hb)]
  simp only [coordinateView,List.getElem_map]

/-- Physical point updates have exactly the list update used by the parser
frame proof; vector capacity and every other coordinate are preserved. -/
theorem coordinateView_set (positions : alloc.vec.Vec tokens.PairPositions) (index : Usize) (position : tokens.PairPositions) :
    coordinateView (positions.set index position) = (coordinateView positions).set index.val (positionValue position) := by
  simp only [coordinateView,alloc.vec.Vec.set_val_eq,List.map_set]

/-- The actual mutable read/backward operation fills the parent closing
coordinate, preserving the already parsed interior and all previous records. -/
theorem close_position_spec (positions : alloc.vec.Vec tokens.PairPositions) (index closing : Usize)
    (leading suffix : List (Nat × Nat)) (opening placeholder : Nat)
    (hview : coordinateView positions = leading ++ (opening,placeholder)::suffix) (hi : index.val = leading.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice tokens.PairPositions) positions index ⦃ output =>
      output.1.«open».val = opening ∧
      coordinateView (output.2 { output.1 with close := closing }) = leading ++ (opening,closing.val)::suffix ⦄ := by
  have hlength := congrArg List.length hview
  simp only [coordinateView_length,List.length_append,List.length_cons] at hlength
  have hb : index.val < positions.length := by omega
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_mono (alloc.vec.Vec.index_mut_usize_spec positions index hb)
  rintro ⟨position,back⟩ ⟨hPosition,hBack⟩
  have hread : positionValue position = (coordinateView positions)[index.val]! := by
    rw [coordinateView_get positions index hb,hPosition]
  have hat : (coordinateView positions)[index.val]! = (opening,placeholder) := by
    rw [hview,hi,List.getElem!_append_right leading ((opening,placeholder)::suffix) leading.length (le_refl _)]
    simp only [Nat.sub_self,List.getElem!_cons_zero]
  have hopen : position.«open».val = opening := congrArg Prod.fst (hread.trans hat)
  refine ⟨hopen,?_⟩
  rw [hBack,coordinateView_set]
  simp only [positionValue,hopen]
  rw [hview,hi,List.set_append_right leading.length (opening,closing.val) (le_refl _)]
  simp only [Nat.sub_self,List.set_cons_zero]

/-- The source threshold cast is exact on both supported pointer widths. -/
theorem u32_max_value : core.num.U32.MAX.val = U32.max := by
  norm_num [core.num.U32.MAX,UScalar.ofNat,UScalar.ofNatCore_val_eq,U32.rMax,U32.max_eq]

theorem u32_max_fits_usize : core.num.U32.MAX.val ≤ UScalar.max .Usize := by
  rw [u32_max_value,UScalar.max_USize_eq]
  rcases Usize.bounds_eq with he | he
  · rw [he]
  · rw [he]
    scalar_tac

end SubtreeProofs.Rust.TokenParser

end
