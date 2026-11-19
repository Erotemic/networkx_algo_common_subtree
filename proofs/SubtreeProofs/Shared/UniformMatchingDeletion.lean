module

public import SubtreeProofs.Shared.UniformMatching
import Mathlib.Tactic

/-!
# Uniform matchings after deleting an original right vertex

Feasible matchings use at most the smaller surviving side. For a complete
uniform instance, attaining this cardinality proves independent optimality.
Filtering the original diagonal is optimal when the right side is no larger
than the left, exactly the corresponding production fast-path case. This is
mathematical correctness, not an actual Rust/f64 source-refinement theorem.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching

variable {L R K : Type*} [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- Deleting one right vertex sharpens the cardinality bound by one on that
side, regardless of weights or the matching implementation. -/
theorem deleted_matching_card_le [Fintype L] [Fintype R]
    (weights : L → R → Option K) (removed : R) (pairs : Finset (L × R))
    (hvalid : Valid (deleteRight weights removed) pairs) :
    pairs.card ≤ min (Fintype.card L) (Fintype.card R - 1) := by
  obtain ⟨hbase, havoid⟩ := (valid_deleteRight_iff weights removed pairs).mp hvalid
  have hsubset : matchedRight pairs ⊆ Finset.univ.erase removed := by
    intro v hv
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ v⟩
    intro he
    exact havoid (he ▸ hv)
  apply le_min
  · rw [← matchedLeft_card hbase]
    exact Finset.card_le_univ _
  · have hc := Finset.card_le_card hsubset
    simpa [matchedRight_card hbase] using hc

/-- The smaller surviving side supplies the true independent upper bound. -/
theorem uniform_deleted_isMaximum_of_card [Fintype L] [Fintype R]
    (value : K) (hvalue : 0 ≤ value) (removed : R) (pairs : Finset (L × R))
    (hvalid : Valid (deleteRight (fun _ _ => some value) removed) pairs)
    (hcard : pairs.card = min (Fintype.card L) (Fintype.card R - 1)) :
    IsMaximum (deleteRight (fun _ _ => some value) removed) pairs := by
  refine ⟨hvalid, ?_⟩
  intro other hother
  have hbound := deleted_matching_card_le (fun _ _ => some value) removed other hother
  have hp := (valid_deleteRight_iff (fun _ _ => some value) removed pairs).mp hvalid
  have ho := (valid_deleteRight_iff (fun _ _ => some value) removed other).mp hother
  rw [weight_deleteRight _ _ _ ho.2, weight_deleteRight _ _ _ hp.2,
    weight_uniform, weight_uniform]
  rw [← hcard] at hbound
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbound) hvalue

omit [IsStrictOrderedRing K] in
/-- Remove incident edges, preserving all original endpoint identities. -/
theorem valid_filter_right (weights : L → R → Option K) (pairs : Finset (L × R))
    (h : Valid weights pairs) (removed : R) :
    Valid (deleteRight weights removed) (pairs.filter (fun p => p.2 ≠ removed)) := by
  apply (valid_deleteRight_iff weights removed _).mpr
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact h.1 p (Finset.mem_filter.mp hp).1
  · intro p hp q hq he
    exact h.2.1 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 he
  · intro p hp q hq he
    exact h.2.2 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 he
  · intro hm
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp hp).2 he

omit [DecidableEq L] in
/-- Projection of the filtered witness is exactly the old endpoint set minus
the deleted original vertex; there is no compact/original index conversion. -/
theorem matchedRight_filter (pairs : Finset (L × R)) (removed : R) :
    matchedRight (pairs.filter (fun p => p.2 ≠ removed)) = (matchedRight pairs).erase removed := by
  unfold matchedRight
  ext v
  constructor
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hp, hn⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_erase.mpr ⟨hn, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  · intro hv
    obtain ⟨hn, hm⟩ := Finset.mem_erase.mp hv
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
    refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, he⟩
    simpa [he] using hn

/-- The diagonal covers every original right vertex when it is the smaller side. -/
theorem diagonalPairs_right_coverage (left right : Nat) (hr : right ≤ left) :
    matchedRight (diagonalPairs left right) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  let i : Fin (min left right) := ⟨v.val, by simp only [min_eq_right hr]; exact v.isLt⟩
  refine Finset.mem_image.mpr ⟨diagonalPair left right i, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · apply Fin.ext
    rfl

/-- Concrete native fast-path shape for deleting a vertex on the smaller right
side: discard only its diagonal pair, retaining optimal surviving indices. -/
theorem diagonalPairs_filter_isMaximum (left right : Nat) (hr : right ≤ left)
    (removed : Fin right) (value : K) (hvalue : 0 ≤ value) :
    IsMaximum (deleteRight (fun _ _ => some value) removed)
      ((diagonalPairs left right).filter (fun p => p.2 ≠ removed)) := by
  have hv := valid_filter_right (fun _ _ => some value) (diagonalPairs left right)
    (diagonalPairs_valid left right value) removed
  apply uniform_deleted_isMaximum_of_card value hvalue removed _ hv
  obtain ⟨hb, _⟩ := (valid_deleteRight_iff (fun _ _ => some value) removed _).mp hv
  rw [← matchedRight_card hb, matchedRight_filter, diagonalPairs_right_coverage left right hr]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ removed), Finset.card_univ, Fintype.card_fin]
  rw [min_eq_right (by omega)]

/-- The smaller-left native branch replaces a deleted diagonal column by
original column `left`, which was previously unused. -/
def switchedPair (left right : Nat) (hl : left < right) (removed : Fin right)
    (i : Fin left) : Fin left × Fin right :=
  (i, if i.val = removed.val then ⟨left, hl⟩ else ⟨i.val, lt_trans i.isLt hl⟩)

def switchedPairs (left right : Nat) (hl : left < right) (removed : Fin right) :
    Finset (Fin left × Fin right) :=
  Finset.univ.image (switchedPair left right hl removed)

theorem switchedPair_right_injective (left right : Nat) (hl : left < right) (removed : Fin right) :
    Function.Injective (fun i => (switchedPair left right hl removed i).2) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have hj := j.isLt
  by_cases hiEq : i.val = removed.val <;> by_cases hjEq : j.val = removed.val
  all_goals simp [switchedPair, hiEq, hjEq] at hv
  all_goals omega

@[simp] theorem switchedPairs_card (left right : Nat) (hl : left < right) (removed : Fin right) :
    (switchedPairs left right hl removed).card = left := by
  unfold switchedPairs
  rw [Finset.card_image_iff.mpr ?_]
  · simp
  · intro i _ j _ he
    exact congrArg Prod.fst he

omit [IsStrictOrderedRing K] in
/-- Both projections remain injective and the deleted original column is absent. -/
theorem switchedPairs_valid (left right : Nat) (hl : left < right) (removed : Fin right) (value : K) :
    Valid (deleteRight (fun _ _ => some value) removed) (switchedPairs left right hl removed) := by
  apply (valid_deleteRight_iff (fun _ _ => some value) removed _).mpr
  refine ⟨⟨by simp, ?_, ?_⟩, ?_⟩
  · intro p hp q hq he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg (switchedPair left right hl removed) he
  · intro p hp q hq he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg (switchedPair left right hl removed) (switchedPair_right_injective left right hl removed he)
  · intro hm
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hv := congrArg Fin.val he
    have hi := i.isLt
    by_cases hiEq : i.val = removed.val
    all_goals simp [switchedPair, hiEq] at hv
    all_goals omega

/-- An unused original column needs no repair: the actual base witness
remains independently maximum after that deletion. -/
theorem diagonalPairs_unused_isMaximum (left right : Nat) (removed : Fin right)
    (hunused : left ≤ removed.val) (value : K) (hvalue : 0 ≤ value) :
    IsMaximum (deleteRight (fun _ _ => some value) removed) (diagonalPairs left right) := by
  apply (diagonalPairs_isMaximum left right value hvalue).deleteRight removed
  intro hm
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hv := congrArg Fin.val he
  change i.val = removed.val at hv
  have hi := i.isLt
  have hb := min_le_left left right
  omega

/-- A full matching survives every right deletion when the right side is
strictly larger. This is independent optimality of the replacement witness. -/
theorem switchedPairs_isMaximum (left right : Nat) (hl : left < right)
    (removed : Fin right) (value : K) (hvalue : 0 ≤ value) :
    IsMaximum (deleteRight (fun _ _ => some value) removed) (switchedPairs left right hl removed) := by
  apply uniform_deleted_isMaximum_of_card value hvalue removed _ (switchedPairs_valid left right hl removed value)
  simp only [switchedPairs_card, Fintype.card_fin]
  rw [min_eq_left (by omega)]

/-- Original-coordinate witness for every deletion in a uniform complete
matrix. These two cases match the production fast-path construction. -/
def uniformRightDeletion (left right : Nat) (removed : Fin right) : Finset (Fin left × Fin right) :=
  if h : right ≤ left then (diagonalPairs left right).filter (fun p => p.2 ≠ removed)
  else if left ≤ removed.val then diagonalPairs left right
  else switchedPairs left right (by omega) removed

/-- Every member of the concrete uniform deletion family is independently
maximum, not merely a feasible restriction of its original optimum. -/
theorem uniformRightDeletion_isMaximum (left right : Nat) (removed : Fin right)
    (value : K) (hvalue : 0 ≤ value) :
    IsMaximum (deleteRight (fun _ _ => some value) removed) (uniformRightDeletion left right removed) := by
  unfold uniformRightDeletion
  split
  · rename_i hr
    exact diagonalPairs_filter_isMaximum left right hr removed value hvalue
  · split
    · rename_i hu
      exact diagonalPairs_unused_isMaximum left right removed hu value hvalue
    · exact switchedPairs_isMaximum left right _ removed value hvalue

end SubtreeProofs.WeightedMatching

end
