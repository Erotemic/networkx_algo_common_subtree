module

public import SubtreeProofs.Paper2004.AnnotatedIsomorphism
public import SubtreeProofs.Paper2004.TokenMaximum
import Mathlib.Tactic

/-! # Independent original-index and token isomorphism optima -/

@[expose] public section

namespace SubtreeProofs.Paper2004.IndexedIso

open IndexedWord OrderedTree TokenEncoding

theorem drop_child (index : Nat) (head tail : Word) : Retains tail (.node index head tail) :=
  Retains.trans (Relation.ReflTransGen.single (Step.root index .nil tail))
    (Retains.keep index (empty_retains head) .refl)

theorem retains_prefix (head tail : Word) : Retains head (append head tail) := by
  induction head with
  | nil => exact empty_retains tail
  | node index inside outside _ ih => exact Retains.keep index .refl ih

/-- Isomorphism pruning is also a contraction, used only to reuse the proved
canonical coordinate reader. The stronger adjacency contract is retained. -/
theorem select_retains {small large : Word} (h : AnnotatedIso.Select small large) : Retains small large := by
  induction h with
  | nil large => exact empty_retains large
  | skip index head _ ih => exact ih.trans (drop_child index head _)
  | keep head tail ihHead ihTail => exact Retains.keep _ ihHead ihTail

theorem region_retains {region source : Word} (h : AnnotatedIso.Region region source) : Retains region source := by
  induction h with
  | refl => exact .refl
  | head index tail _ ih =>
    exact ih.trans ((retains_prefix _ tail).trans (Relation.ReflTransGen.single (Step.root index _ tail)))
  | tail index head _ ih => exact ih.trans (drop_child index head _)

def Prunes (rooted : Bool) (small large : Word) : Prop :=
  if rooted then AnnotatedIso.Prunes small large else AnnotatedIso.AnyPrunes small large

theorem prunes_retains {rooted : Bool} {small large : Word} (h : Prunes rooted small large) : Retains small large := by
  cases rooted with
  | true => exact select_retains h.select
  | false =>
    obtain ⟨region,hRegion,hPrunes⟩ := h
    exact (select_retains hPrunes.select).trans (region_retains hRegion)

def MaximumShape (rooted : Bool) (candidate left right : OrderedTree) : Prop :=
  if rooted then IsMaximumRootedIsomorphism candidate left right else IsMaximumIsomorphism candidate left right

def Maximum (rooted : Bool) (left right : DyckWord) (leftWitness rightWitness : Word) (score : Nat) : Prop :=
  Prunes rooted leftWitness (numberFrom left.toTree 0) ∧
    Prunes rooted rightWitness (numberFrom right.toTree 0) ∧
    erase leftWitness = erase rightWitness ∧
    MaximumShape rooted (decodeDyck (erase leftWitness)) (decodeDyck left) (decodeDyck right) ∧
    score = (erase leftWitness).semilength

/-- Original coordinates, independent whole-subtree pruning and independent
global optimality; no parser, Rust solver or reconstruction procedure appears. -/
def MaximumTokens (rooted : Bool) (left right : List Bool) (leftIndices rightIndices : List Nat) (score : Nat) : Prop :=
  ∃ leftWord rightWord : DyckWord, ∃ leftWitness rightWitness : Word,
    left = encoded leftWord ∧ right = encoded rightWord ∧ Maximum rooted leftWord rightWord leftWitness rightWitness score ∧
    leftIndices = tokenIndices (fun index => (positionPairs leftWord.toTree 0)[index]!) leftWitness ∧
    rightIndices = tokenIndices (fun index => (positionPairs rightWord.toTree 0)[index]!) rightWitness ∧
    leftIndices.Sublist (List.range left.length) ∧ rightIndices.Sublist (List.range right.length) ∧
    leftIndices.map (fun index => left[index]!) = encoded (erase leftWitness) ∧
    rightIndices.map (fun index => right[index]!) = encoded (erase leftWitness)

theorem maximum_tokens (rooted : Bool) (left right : DyckWord) (leftWitness rightWitness : Word) (score : Nat)
    (h : Maximum rooted left right leftWitness rightWitness score) :
    MaximumTokens rooted (encoded left) (encoded right)
      (tokenIndices (fun index => (positionPairs left.toTree 0)[index]!) leftWitness)
      (tokenIndices (fun index => (positionPairs right.toTree 0)[index]!) rightWitness) score := by
  have hl := prunes_retains h.1
  have hr := prunes_retains h.2.1
  refine ⟨left,right,leftWitness,rightWitness,rfl,rfl,h,rfl,rfl,
    retained_token_sublist left leftWitness hl,retained_token_sublist right rightWitness hr,
    retained_readsTokens left leftWitness hl,?_⟩
  have hh := retained_readsTokens right rightWitness hr
  rw [ReadsTokens,← h.2.2.1] at hh
  exact hh

/-- Each source token witness contains exactly two endpoints per scored pair. -/
theorem MaximumTokens.lengths {rooted : Bool} {left right : List Bool} {leftIndices rightIndices : List Nat} {score : Nat}
    (h : MaximumTokens rooted left right leftIndices rightIndices score) :
    leftIndices.length = 2*score ∧ rightIndices.length = 2*score := by
  obtain ⟨_,_,_,_,_,_,hMaximum,_,_,_,_,hl,hr⟩ := h
  have hll := congrArg List.length hl
  have hrl := congrArg List.length hr
  simpa only [List.length_map,encoded_length,hMaximum.2.2.2.2] using And.intro hll hrl

theorem MaximumTokens.indices_valid {rooted : Bool} {left right : List Bool} {leftIndices rightIndices : List Nat} {score : Nat}
    (h : MaximumTokens rooted left right leftIndices rightIndices score) :
    leftIndices.Nodup ∧ rightIndices.Nodup ∧
      (∀ index ∈ leftIndices, index < left.length) ∧ (∀ index ∈ rightIndices, index < right.length) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hl,hr,_,_⟩ := h
  exact ⟨hl.nodup List.nodup_range,hr.nodup List.nodup_range,
    fun index hi => List.mem_range.mp (hl.subset hi),fun index hi => List.mem_range.mp (hr.subset hi)⟩

end SubtreeProofs.Paper2004.IndexedIso

end
