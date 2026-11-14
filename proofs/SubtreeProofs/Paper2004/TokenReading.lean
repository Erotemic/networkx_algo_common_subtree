module

public import SubtreeProofs.Paper2004.CanonicalTokenPositions
import Mathlib.Tactic

/-! # Reading retained original coordinates reconstructs the retained Dyck word -/

@[expose] public section

namespace SubtreeProofs.Paper2004.TokenEncoding

open IndexedWord

/-- The original token array read through an indexed witness spells its shape. -/
def ReadsTokens (input : List Bool) (positions : Nat → Nat × Nat) (word : Word) : Prop :=
  (tokenIndices positions word).map (fun index => input[index]!) = encoded (erase word)

/-- Both endpoints of each retained original pair have their specified kinds. -/
def PairKinds (input : List Bool) (positions : Nat → Nat × Nat) (word : Word) : Prop :=
  ∀ index ∈ indices word, input[(positions index).1]! = false ∧ input[(positions index).2]! = true

theorem readsTokens_node_iff (input : List Bool) (positions : Nat → Nat × Nat) (index : Nat) (head tail : Word) :
    ReadsTokens input positions (.node index head tail) ↔
      input[(positions index).1]! = false ∧ ReadsTokens input positions head ∧
      input[(positions index).2]! = true ∧ ReadsTokens input positions tail := by
  unfold ReadsTokens
  simp only [tokenIndices,List.map_cons,List.map_append,erase,encoded_nest_add]
  constructor
  · intro he
    obtain ⟨hopen,hrest⟩ := List.cons.inj he
    have hlength : ((tokenIndices positions head).map (fun index => input[index]!)).length = (encoded (erase head)).length := by
      simp only [List.length_map,tokenIndices_length,encoded_length,erase_semilength]
    obtain ⟨hhead,ht⟩ := List.append_inj hrest hlength
    obtain ⟨hclose,htail⟩ := List.cons.inj ht
    exact ⟨hopen,hhead,hclose,htail⟩
  · rintro ⟨hopen,hhead,hclose,htail⟩
    rw [hopen,hhead,hclose,htail]

/-- Global spelling equality is equivalent to the kind of each original pair;
this equivalence preserves the witness's full order and nesting. -/
theorem readsTokens_iff_pairKinds (input : List Bool) (positions : Nat → Nat × Nat) (word : Word) :
    ReadsTokens input positions word ↔ PairKinds input positions word := by
  induction word with
  | nil => simp [ReadsTokens,PairKinds,tokenIndices,indices,erase]
  | node index head tail ihHead ihTail =>
    rw [readsTokens_node_iff,ihHead,ihTail]
    constructor
    · rintro ⟨ho,hh,hc,ht⟩ i hm
      simp only [indices,List.mem_cons,List.mem_append] at hm
      rcases hm with rfl | hm | hm
      · exact ⟨ho,hc⟩
      · exact hh i hm
      · exact ht i hm
    · intro h
      have hr := h index (by simp only [indices,List.mem_cons]; exact Or.inl True.intro)
      refine ⟨hr.1,?_,hr.2,?_⟩
      · intro i hm
        exact h i (by simp only [indices,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hm))
      · intro i hm
        exact h i (by simp only [indices,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hm))

/-- Pair deletion cannot change the original endpoint kinds of any survivor. -/
theorem readsTokens_retains (input : List Bool) (positions : Nat → Nat × Nat) {small large : Word}
    (h : Retains small large) (hread : ReadsTokens input positions large) : ReadsTokens input positions small := by
  rw [readsTokens_iff_pairKinds] at hread ⊢
  exact fun index hi => hread index (h.indices_sublist.subset hi)

/-- Reading the complete zero-based coordinate range returns the original array. -/
theorem map_read_range (input : List Bool) :
    (List.range input.length).map (fun index => input[index]!) = input := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro index hleft hright
    simp only [List.getElem_map,List.getElem_range]
    exact getElem!_pos input index hright

/-- The canonical original pair table spells the original independent Dyck word. -/
theorem canonical_readsTokens (word : DyckWord) :
    ReadsTokens (encoded word) (fun index => (positionPairs word.toTree 0)[index]!) (numberFrom word.toTree 0) := by
  unfold ReadsTokens
  rw [canonical_tokenIndices_zero,DyckWord.numNodes_toTree,erase_numberFrom,DyckWord.ofTree_toTree,← encoded_length,map_read_range]

/-- Every retained indexed witness, read at its exact original coordinates,
spells the retained balanced word. This applies to arbitrary pair deletions,
independently of the optimizer or parser. -/
theorem retained_readsTokens (word : DyckWord) (small : Word) (h : Retains small (numberFrom word.toTree 0)) :
    ReadsTokens (encoded word) (fun index => (positionPairs word.toTree 0)[index]!) small :=
  readsTokens_retains _ _ h (canonical_readsTokens word)

end SubtreeProofs.Paper2004.TokenEncoding

end
