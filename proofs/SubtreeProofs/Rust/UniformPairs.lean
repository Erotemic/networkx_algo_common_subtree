module

public import SubtreeProofs.Rust.AssignmentInitialization
public import SubtreeProofs.Shared.UniformMatchingDeletion
import Mathlib.Tactic

/-!
# Production uniform-matching index construction

The actual integer-only Rust helper returns original coordinates, terminates,
and respects index and deletion bounds. Its base and deleted outputs refine
independent finite matching optima over an ordered ring. Floating-point uniform
recognition and score accumulation remain outside these source theorems.
-/

@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core.uniform_pairs

namespace SubtreeProofs.Rust.UniformPairs

def pairValue (p : Usize × Usize) : Nat × Nat := (p.1.val, p.2.val)

def pairAt (left right : Nat) (deleted : Option Nat) (row : Nat) : Option (Nat × Nat) :=
  match deleted with
  | none => some (row, row)
  | some removed =>
    if left < right then some (row, if row = removed then left else row)
    else if row = removed then none else some (row, row)

def pairPrefix (left right : Nat) (deleted : Option Nat) (count : Nat) : List (Nat × Nat) :=
  (List.range count).filterMap (pairAt left right deleted)

theorem prefix_length (left right : Nat) (deleted : Option Nat) (count : Nat) :
    (pairPrefix left right deleted count).length ≤ count := by
  simpa [pairPrefix] using List.length_filterMap_le (pairAt left right deleted) (List.range count)

theorem prefix_succ (left right : Nat) (deleted : Option Nat) (count : Nat) :
    pairPrefix left right deleted (count + 1) = pairPrefix left right deleted count ++
      (pairAt left right deleted count).toList := by
  cases h : pairAt left right deleted count <;> simp [pairPrefix, List.range_succ, List.filterMap_append, h]

theorem row_spec (left right row : Usize) (deleted : Option Usize) :
    uniform_row left right deleted row ⦃ result =>
      result.map pairValue = pairAt left.val right.val (deleted.map UScalar.val) row.val ⦄ := by
  cases deleted with
  | none => simp [uniform_row, pairAt, pairValue]
  | some removed =>
    simp only [uniform_row]
    split
    · rename_i hlt
      have hlt' : left.val < right.val := by scalar_tac
      split
      · rename_i he
        subst row
        simp [pairAt, pairValue, hlt']
      · rename_i he
        have hn : row.val ≠ removed.val := fun h => he (UScalar.eq_of_val_eq h)
        simp [pairAt, pairValue, hlt', hn]
    · rename_i hlt
      have hlt' : ¬ left.val < right.val := by scalar_tac
      split
      · rename_i he
        subst row
        simp [pairAt, hlt']
      · rename_i he
        have hn : row.val ≠ removed.val := fun h => he (UScalar.eq_of_val_eq h)
        simp [pairAt, pairValue, hlt', hn]

theorem append_spec (left right row : Usize) (deleted : Option Usize)
    (pairs : alloc.vec.Vec (Usize × Usize)) (entry : Option (Usize × Usize))
    (hLen : pairs.val.length < Usize.max)
    (hRep : pairs.val.map pairValue = pairPrefix left.val right.val (deleted.map UScalar.val) row.val)
    (hEntry : entry.map pairValue = pairAt left.val right.val (deleted.map UScalar.val) row.val) :
    (match entry with | none => ok pairs | some p => alloc.vec.Vec.push pairs p)
      ⦃ result => result.val.map pairValue = pairPrefix left.val right.val (deleted.map UScalar.val) (row.val + 1) ⦄ := by
  cases entry with
  | none =>
    apply (WP.spec_ok _).mpr
    rw [prefix_succ, ← hEntry]
    simpa using hRep
  | some p =>
    apply WP.spec_mono (alloc.vec.Vec.push_spec pairs p hLen)
    intro result hResult
    rw [hResult, List.map_append, List.map_singleton, hRep, prefix_succ, ← hEntry]
    rfl

theorem loop_spec (left right limit : Usize) (deleted : Option Usize) :
    uniform_pair_indices_loop left right deleted limit (alloc.vec.Vec.new (Usize × Usize)) 0#usize
      ⦃ result => result.val.map pairValue = pairPrefix left.val right.val (deleted.map UScalar.val) limit.val ⦄ := by
  unfold uniform_pair_indices_loop
  apply loop.spec_decr_nat (fun state => limit.val - state.2.val)
    (fun state => state.2.val ≤ limit.val ∧ state.1.val.map pairValue =
      pairPrefix left.val right.val (deleted.map UScalar.val) state.2.val)
    _ _ _ ?_ (by simp [pairPrefix])
  rintro ⟨pairs,row⟩ ⟨hi,hRep⟩
  simp only [uniform_pair_indices_loop.body]
  split
  · rename_i hlt
    have hBound := prefix_length left.val right.val (deleted.map UScalar.val) row.val
    rw [← hRep, List.length_map] at hBound
    have hLen : pairs.val.length < Usize.max := by scalar_tac
    apply WP.spec_bind (row_spec left right row deleted)
    intro entry hEntry
    apply WP.spec_bind (append_spec left right row deleted pairs entry hLen hRep hEntry)
    intro result hResult
    apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
    intro row1 hRow1
    simp only [WP.spec_ok]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · scalar_tac
    · have hv : row1.val = row.val + 1 := by scalar_tac
      rw [hv]
      exact hResult
    · scalar_tac
  · rename_i hnot
    apply (WP.spec_ok _).mpr
    have he : row.val = limit.val := by scalar_tac
    exact hRep.trans (congrArg (pairPrefix left.val right.val (deleted.map UScalar.val)) he)

theorem indices_spec (left right : Usize) (deleted : Option Usize) :
    uniform_pair_indices left right deleted ⦃ result =>
      result.val.map pairValue = pairPrefix left.val right.val (deleted.map UScalar.val) (min left.val right.val) ⦄ := by
  unfold uniform_pair_indices
  split
  · rename_i hlt
    have hlt' : left.val ≤ right.val := by scalar_tac
    simpa only [bind_ok, alloc.vec.Vec.with_capacity, min_eq_left hlt'] using loop_spec left right left deleted
  · rename_i hnot
    have hle : right.val ≤ left.val := by scalar_tac
    simpa only [bind_ok, alloc.vec.Vec.with_capacity, min_eq_right hle] using loop_spec left right right deleted

theorem pairAt_first (left right row : Nat) (deleted : Option Nat) (p : Nat × Nat)
    (hp : pairAt left right deleted row = some p) : p.1 = row := by
  cases deleted with
  | none => simpa [pairAt, eq_comm] using congrArg (fun o => o.map Prod.fst) hp
  | some removed =>
    by_cases hl : left < right <;> by_cases he : row = removed
    all_goals simp [pairAt, hl, he] at hp
    all_goals cases hp; simp_all

theorem pairAt_valid (left right row : Nat) (deleted : Option Nat) (p : Nat × Nat)
    (hrow : row < min left right) (hp : pairAt left right deleted row = some p) :
    p.1 < left ∧ p.2 < right ∧ ∀ r, deleted = some r → p.2 ≠ r := by
  have hl : row < left := lt_of_lt_of_le hrow (min_le_left _ _)
  have hr : row < right := lt_of_lt_of_le hrow (min_le_right _ _)
  cases deleted with
  | none => simp [pairAt] at hp; cases hp; simp_all
  | some removed =>
    by_cases hh : left < right <;> by_cases he : row = removed
    all_goals simp [pairAt, hh, he] at hp
    all_goals cases hp
    all_goals simp_all
    all_goals omega

theorem prefix_rows (left right count : Nat) (deleted : Option Nat) :
    (pairPrefix left right deleted count).map Prod.fst =
      (List.range count).filter (fun row => (pairAt left right deleted row).isSome) := by
  unfold pairPrefix
  rw [List.map_filterMap]
  have he : (fun i => (pairAt left right deleted i).map Prod.fst) =
      (fun i => if (pairAt left right deleted i).isSome then some i else none) := by
    funext i
    cases h : pairAt left right deleted i with
    | none => simp
    | some p => simp [pairAt_first left right i deleted p h]
  rw [he]
  change (List.range count).filterMap (Option.guard (fun i => (pairAt left right deleted i).isSome)) = _
  rw [List.filterMap_eq_filter]

theorem prefix_rows_nodup (left right count : Nat) (deleted : Option Nat) :
    ((pairPrefix left right deleted count).map Prod.fst).Nodup := by
  rw [prefix_rows]
  exact List.Nodup.filter _ List.nodup_range

open SubtreeProofs.WeightedMatching

def finiteValue {left right : Nat} (p : Fin left × Fin right) : Nat × Nat := (p.1.val, p.2.val)

def coordinates {left right : Nat} (pairs : Finset (Fin left × Fin right)) : Finset (Nat × Nat) :=
  pairs.image finiteValue

theorem base_coordinates (left right : Nat) :
    (pairPrefix left right none (min left right)).toFinset = coordinates (diagonalPairs left right) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hp)
    let j : Fin (min left right) := ⟨i, List.mem_range.mp hi⟩
    refine Finset.mem_image.mpr ⟨diagonalPair left right j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, ?_⟩
    change (i, i) = p
    exact Option.some.inj he
  · intro hp
    obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hOriginal
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)

theorem switched_projection (left right : Nat) (hl : left < right) (removed : Fin right) (i : Fin left) :
    some (finiteValue (switchedPair left right hl removed i)) = pairAt left right (some removed.val) i.val := by
  by_cases he : i.val = removed.val
  all_goals simp [pairAt, hl, switchedPair, finiteValue, he]

theorem switched_coordinates (left right : Nat) (hl : left < right) (removed : Fin right) :
    (pairPrefix left right (some removed.val) (min left right)).toFinset =
      coordinates (switchedPairs left right hl removed) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hp)
    let j : Fin left := ⟨i, lt_of_lt_of_le (List.mem_range.mp hi) (min_le_left _ _)⟩
    refine Finset.mem_image.mpr ⟨switchedPair left right hl removed j,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, ?_⟩
    exact Option.some.inj ((switched_projection left right hl removed j).trans he)
  · intro hp
    obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hOriginal
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    refine ⟨i.val, List.mem_range.mpr (by simpa only [min_eq_left hl.le] using i.isLt), ?_⟩
    exact (switched_projection left right hl removed i).symm

theorem prefix_remove (left right removed count : Nat) (hr : right ≤ left) :
    pairPrefix left right (some removed) count =
      (pairPrefix left right none count).filter (fun p => decide (p.2 ≠ removed)) := by
  induction count with
  | zero => simp [pairPrefix]
  | succ count ih =>
    rw [prefix_succ, prefix_succ, List.filter_append, ih]
    by_cases he : count = removed
    all_goals simp [pairAt, not_lt_of_ge hr, he]

theorem coordinates_filter {left right : Nat} (pairs : Finset (Fin left × Fin right)) (removed : Fin right) :
    coordinates (pairs.filter (fun p => p.2 ≠ removed)) =
      (coordinates pairs).filter (fun p => p.2 ≠ removed.val) := by
  unfold coordinates
  ext p
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨original, ⟨hOriginal, hNe⟩, rfl⟩
    refine ⟨⟨original, hOriginal, rfl⟩, ?_⟩
    intro he
    exact hNe (Fin.ext he)
  · rintro ⟨⟨original, hOriginal, rfl⟩, hNe⟩
    refine ⟨original, ⟨hOriginal, ?_⟩, rfl⟩
    intro he
    exact hNe (congrArg Fin.val he)

theorem filtered_coordinates (left right : Nat) (hr : right ≤ left) (removed : Fin right) :
    (pairPrefix left right (some removed.val) (min left right)).toFinset =
      coordinates ((diagonalPairs left right).filter (fun p => p.2 ≠ removed)) := by
  rw [coordinates_filter, prefix_remove left right removed.val _ hr]
  ext p
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, decide_eq_true_eq]
  apply and_congr ?_ Iff.rfl
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp (base_coordinates left right) p

/-- The actual translated source returns exact original coordinates of an
independently maximum matching after every valid right deletion. -/
theorem source_deleted_maximum {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (left right removed : Usize) (hRemoved : removed.val < right.val) (value : K) (hValue : 0 ≤ value) :
    uniform_pair_indices left right (some removed) ⦃ result =>
      ∃ witness : Finset (Fin left.val × Fin right.val),
        IsMaximum (deleteRight (fun _ _ => some value) (⟨removed.val, hRemoved⟩ : Fin right.val)) witness ∧
        (result.val.map pairValue).toFinset = coordinates witness ∧
        ((result.val.map pairValue).map Prod.fst).Nodup ⦄ := by
  apply WP.spec_mono (indices_spec left right (some removed))
  intro result hResult
  simp only [Option.map_some] at hResult
  have hn := prefix_rows_nodup left.val right.val (min left.val right.val) (some removed.val)
  by_cases hr : right.val ≤ left.val
  · refine ⟨(diagonalPairs left.val right.val).filter (fun p => p.2 ≠ (⟨removed.val, hRemoved⟩ : Fin right.val)),
      diagonalPairs_filter_isMaximum _ _ hr _ value hValue, ?_, ?_⟩
    · rw [hResult]
      exact filtered_coordinates left.val right.val hr ⟨removed.val, hRemoved⟩
    · simpa only [← hResult] using hn
  · have hl : left.val < right.val := by omega
    refine ⟨switchedPairs left.val right.val hl ⟨removed.val, hRemoved⟩,
      switchedPairs_isMaximum _ _ hl _ value hValue, ?_, ?_⟩
    · rw [hResult]
      exact switched_coordinates left.val right.val hl ⟨removed.val, hRemoved⟩
    · simpa only [← hResult] using hn

theorem source_base_maximum {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (left right : Usize) (value : K) (hValue : 0 ≤ value) :
    uniform_pair_indices left right none ⦃ result =>
      ∃ witness : Finset (Fin left.val × Fin right.val),
        IsMaximum (fun _ _ => some value) witness ∧
        (result.val.map pairValue).toFinset = coordinates witness ∧
        ((result.val.map pairValue).map Prod.fst).Nodup ⦄ := by
  apply WP.spec_mono (indices_spec left right none)
  intro result hResult
  simp only [Option.map_none] at hResult
  refine ⟨diagonalPairs left.val right.val, diagonalPairs_isMaximum _ _ value hValue, ?_, ?_⟩
  · rw [hResult]
    exact base_coordinates _ _
  · rw [hResult]
    exact prefix_rows_nodup _ _ _ _

/-- Bounds and deletion exclusion apply to every returned source vector entry,
including empty dimensions and out-of-range deletions. -/
theorem source_index_bounds (left right : Usize) (deleted : Option Usize) :
    uniform_pair_indices left right deleted ⦃ result =>
      ∀ p ∈ result.val, p.1.val < left.val ∧ p.2.val < right.val ∧
        ∀ r, deleted = some r → p.2 ≠ r ⦄ := by
  apply WP.spec_mono (indices_spec left right deleted)
  intro result hResult p hp
  have hm : pairValue p ∈ pairPrefix left.val right.val (deleted.map UScalar.val) (min left.val right.val) := by
    rw [← hResult]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hm
  have hv := pairAt_valid left.val right.val i (deleted.map UScalar.val) (pairValue p) (List.mem_range.mp hi) he
  refine ⟨hv.1, hv.2.1, ?_⟩
  intro r hd heq
  have hNat : deleted.map UScalar.val = some r.val := by simp [hd]
  exact hv.2.2 r.val hNat (congrArg UScalar.val heq)

/-- The source vector has no duplicate rows or pairs. Its actual length equals
its represented pair-set cardinality and is bounded by the smaller side.
This counts live entries, not allocator capacity or a machine memory trace. -/
theorem source_pair_cells (left right : Usize) (deleted : Option Usize) :
    uniform_pair_indices left right deleted ⦃ result =>
      ((result.val.map pairValue).map Prod.fst).Nodup ∧
      result.val.length = (result.val.map pairValue).toFinset.card ∧
      result.val.length ≤ min left.val right.val ⦄ := by
  apply WP.spec_mono (indices_spec left right deleted)
  intro result hResult
  have hRows : ((result.val.map pairValue).map Prod.fst).Nodup := by
    rw [hResult]
    exact prefix_rows_nodup _ _ _ _
  have hPairs := hRows.of_map Prod.fst
  refine ⟨hRows, ?_, ?_⟩
  · simpa only [List.length_map] using (List.toFinset_card_of_nodup hPairs).symm
  · have hBound := prefix_length left.val right.val (deleted.map UScalar.val) (min left.val right.val)
    rw [← hResult, List.length_map] at hBound
    exact hBound

end SubtreeProofs.Rust.UniformPairs

end
