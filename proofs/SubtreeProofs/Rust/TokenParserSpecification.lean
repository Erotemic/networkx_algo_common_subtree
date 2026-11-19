module

public import SubtreeProofs.Rust.TokenParserRepresentation
import Mathlib.Tactic

/-! # Exact parsed shape, stopping counter and original coordinate-table content -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.TokenParser

open OrderedSolver IndexedOrderedSolver Paper2004.TokenEncoding

/-- The complete independently specified content of an accepted parsed segment.
The prior coordinate records remain unchanged; all new records are exact
original token positions in canonical pair preorder. -/
structure ParsedAs (word : BalancedWord) (start : Usize) (initial : alloc.vec.Vec tokens.PairPositions)
    (result : tokens.ParsedForest) : Prop where
  word_eq : result.word = word
  next_eq : result.next.val = start.val+(wordTokens word).length
  coordinates : coordinateView result.positions = coordinateView initial ++ positionPairs (sourceShape word) start.val

/-- Parsed coordinate count is derived from content, not supplied separately. -/
theorem ParsedAs.positions_length (word : BalancedWord) (start : Usize) (initial : alloc.vec.Vec tokens.PairPositions)
    (result : tokens.ParsedForest) (h : ParsedAs word start initial result) :
    result.positions.length = initial.length+(toDyck word).semilength := by
  have he := congrArg List.length h.coordinates
  simpa only [coordinateView_length,List.length_append,positionPairs_length,sourceShape_nodes] using he

/-- The actual indexed token read safely returns an independently known token
at the boundary after the exact preceding input segment. -/
theorem read_token_spec (input : Slice Bool) (index : Usize) (leading rest : List Bool) (value : Bool)
    (hinput : input.val = leading ++ value::rest) (hindex : index.val = leading.length) :
    Slice.index_usize input index ⦃ result => result = value ⦄ := by
  have hlength : input.length = leading.length+1+rest.length := by
    simp only [Slice.length,hinput,List.length_append,List.length_cons]
    omega
  have hi : index.val < input.length := by omega
  have hv : input.val[index.val]! = value := by
    rw [hinput,hindex,List.getElem!_append_right leading (value::rest) leading.length (le_refl _)]
    simp only [Nat.sub_self,List.getElem!_cons_zero]
  apply WP.spec_mono (Slice.index_usize_spec input index hi)
  intro result hResult
  have he : result = input.val[index.val]! := by simpa only [getElem!_pos input.val index.val hi] using hResult
  exact he.trans hv

/-- Every parsed segment's next counter remains within the actual original
array, as a consequence of exact input contents and the specified start. -/
theorem ParsedAs.next_bound (input : Slice Bool) (word : BalancedWord) (start : Usize)
    (initial : alloc.vec.Vec tokens.PairPositions) (result : tokens.ParsedForest) (leading suffix : List Bool)
    (hinput : input.val = leading ++ wordTokens word ++ suffix) (hstart : start.val = leading.length)
    (h : ParsedAs word start initial result) : result.next.val ≤ input.length := by
  have hlength : input.length = leading.length+(wordTokens word).length+suffix.length := by
    simp only [Slice.length,hinput,List.length_append]
  have hn := h.next_eq
  omega

end SubtreeProofs.Rust.TokenParser

end
