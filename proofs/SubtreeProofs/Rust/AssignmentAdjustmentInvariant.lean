module

public import SubtreeProofs.Rust.AssignmentAdjustment
import Mathlib.Tactic

/-!
# Prefix invariants for actual potential adjustment

Used-column pointers form an injective row family. Consequently each selected
row is updated once, even though the source iterates over column indices.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAdjustmentInvariant

open AssignmentColumnScan AssignmentScanInvariant

/-- A numerical view of every physical vector slot, retaining exact length. -/
def Frame {T S : Type*} [Inhabited T] (initial current : alloc.vec.Vec T)
    (view : T → S) (expected : Nat → S) : Prop :=
  current.length = initial.length ∧ ∀ index < initial.length, view current.val[index]! = expected index

theorem frame_set {T S : Type*} [Inhabited T] (initial current : alloc.vec.Vec T) (view : T → S)
    (before after : Nat → S) (index : Usize) (value : T)
    (hframe : Frame initial current view before) (hindex : index.val < initial.length)
    (hvalue : view value = after index.val)
    (hother : ∀ other < initial.length, other ≠ index.val → after other = before other) :
    Frame initial (current.set index value) view after := by
  rcases hframe with ⟨hlen,hvalues⟩
  refine ⟨by simpa using hlen, ?_⟩
  intro other ho
  by_cases he : other = index.val
  · subst other
    rw [vec_set_self current index value (by omega)]
    exact hvalue
  · rw [vec_set_other current index value other (by omega) (Ne.symm he)]
    exact (hvalues other ho).trans (hother other ho he).symm

theorem frame_unchanged {T S : Type*} [Inhabited T] (initial current : alloc.vec.Vec T) (view : T → S)
    (before after : Nat → S) (hframe : Frame initial current view before)
    (heq : ∀ index < initial.length, after index = before index) : Frame initial current view after :=
  ⟨hframe.1, fun index hi => (hframe.2 index hi).trans (heq index hi).symm⟩

def usedIndices (used : Slice Bool) (cursor : Nat) : Finset Nat :=
  (Finset.range cursor).filter (fun index => used.val[index]! = true)

@[simp] theorem mem_usedIndices (used : Slice Bool) (cursor index : Nat) :
    index ∈ usedIndices used cursor ↔ index < cursor ∧ used.val[index]! = true := by
  simp [usedIndices]

def usedRows (matched : Slice Usize) (used : Slice Bool) (cursor : Nat) : Finset Nat :=
  (usedIndices used cursor).image (fun index => matched.val[index]!.val)

@[simp] theorem mem_usedRows (matched : Slice Usize) (used : Slice Bool) (cursor row : Nat) :
    row ∈ usedRows matched used cursor ↔ ∃ index, index < cursor ∧ used.val[index]! = true ∧ matched.val[index]!.val = row := by
  simp [usedRows, and_assoc]

theorem usedIndices_succ (used : Slice Bool) (cursor : Nat) :
    usedIndices used (cursor+1) = if used.val[cursor]! then insert cursor (usedIndices used cursor) else usedIndices used cursor := by
  unfold usedIndices
  rw [Finset.range_add_one, Finset.filter_insert]

theorem usedRows_succ (matched : Slice Usize) (used : Slice Bool) (cursor : Nat) :
    usedRows matched used (cursor+1) =
      if used.val[cursor]! then insert matched.val[cursor]!.val (usedRows matched used cursor) else usedRows matched used cursor := by
  by_cases hflag : used.val[cursor]! = true <;>
    simp only [usedRows, usedIndices_succ, hflag, Bool.false_eq_true, ↓reduceIte, Finset.image_insert]

/-- Pointer injectivity is required only on the actually used columns. -/
def UsedInjective (matched : Slice Usize) (used : Slice Bool) (n : Usize) : Prop :=
  ∀ first, first ≤ n.val → used.val[first]! = true →
    ∀ second, second ≤ n.val → used.val[second]! = true →
      matched.val[first]!.val = matched.val[second]!.val → first = second

/-- The next used column points to a row that has not yet been adjusted. -/
theorem assigned_not_processed (matched : Slice Usize) (used : Slice Bool) (n : Usize) (cursor : Nat)
    (hinjective : UsedInjective matched used n) (hc : cursor ≤ n.val) (hflag : used.val[cursor]! = true) :
    matched.val[cursor]!.val ∉ usedRows matched used cursor := by
  intro hmem
  obtain ⟨previous,hprevious,hused,heq⟩ := (mem_usedRows matched used cursor _).mp hmem
  have hsame := hinjective previous (by omega) hused cursor hc hflag heq
  omega

def rowExpected (initial : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (amount : I128) (cursor row : Nat) : ℤ :=
  initial.val[row]!.val + if row ∈ usedRows matched used cursor then amount.val else 0

def columnExpected (initial : alloc.vec.Vec I128) (used : Slice Bool) (amount : I128) (cursor col : Nat) : ℤ :=
  initial.val[col]!.val - if col ∈ usedIndices used cursor then amount.val else 0

def slackExpected (initial : alloc.vec.Vec (Option I128)) (used : Slice Bool) (amount : I128) (cursor col : Nat) : WithTop ℤ :=
  if col < cursor ∧ used.val[col]! = false then slackValue initial.val[col]! + ((-amount.val : ℤ) : WithTop ℤ)
  else slackValue initial.val[col]!


theorem rowExpected_used (initial : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (amount : I128) (cursor row : Nat) (hflag : used.val[cursor]! = true) :
    rowExpected initial matched used amount (cursor+1) row =
      if row = matched.val[cursor]!.val then initial.val[row]!.val + amount.val
      else rowExpected initial matched used amount cursor row := by
  by_cases he : row = matched.val[cursor]!.val <;>
    simp only [rowExpected, usedRows_succ, hflag, ↓reduceIte, Finset.mem_insert, he, eq_self, true_or, false_or]

theorem columnExpected_used (initial : alloc.vec.Vec I128) (used : Slice Bool)
    (amount : I128) (cursor col : Nat) (hflag : used.val[cursor]! = true) :
    columnExpected initial used amount (cursor+1) col =
      if col = cursor then initial.val[col]!.val - amount.val
      else columnExpected initial used amount cursor col := by
  by_cases he : col = cursor <;>
    simp only [columnExpected, usedIndices_succ, hflag, ↓reduceIte, Finset.mem_insert, he, eq_self, true_or, false_or]

theorem rowExpected_unused (initial : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (amount : I128) (cursor row : Nat) (hflag : used.val[cursor]! = false) :
    rowExpected initial matched used amount (cursor+1) row =
      rowExpected initial matched used amount cursor row := by
  simp only [rowExpected, usedRows_succ, hflag, Bool.false_eq_true, ↓reduceIte]

theorem columnExpected_unused (initial : alloc.vec.Vec I128) (used : Slice Bool)
    (amount : I128) (cursor col : Nat) (hflag : used.val[cursor]! = false) :
    columnExpected initial used amount (cursor+1) col = columnExpected initial used amount cursor col := by
  simp only [columnExpected, usedIndices_succ, hflag, Bool.false_eq_true, ↓reduceIte]

theorem slackExpected_other (initial : alloc.vec.Vec (Option I128)) (used : Slice Bool)
    (amount : I128) (cursor col : Nat) (hne : col ≠ cursor) :
    slackExpected initial used amount (cursor+1) col = slackExpected initial used amount cursor col := by
  have he : col < cursor+1 ↔ col < cursor := by omega
  simp only [slackExpected, he]

theorem slackExpected_used (initial : alloc.vec.Vec (Option I128)) (used : Slice Bool)
    (amount : I128) (cursor col : Nat) (hflag : used.val[cursor]! = true) :
    slackExpected initial used amount (cursor+1) col = slackExpected initial used amount cursor col := by
  by_cases he : col = cursor
  · subst col
    simp only [slackExpected, hflag, Bool.true_eq_false, and_false, ↓reduceIte]
  · exact slackExpected_other initial used amount cursor col he


theorem slackFrame_unprocessed (initial current : alloc.vec.Vec (Option I128)) (used : Slice Bool)
    (amount : I128) (cursor : Nat) (hc : cursor < initial.length)
    (hframe : Frame initial current slackValue (slackExpected initial used amount cursor)) :
    current.val[cursor]! = initial.val[cursor]! := by
  apply slackValue_injective
  simpa only [slackExpected, Nat.lt_irrefl, false_and, ↓reduceIte] using hframe.2 cursor hc

theorem slackFrame_none (initial current : alloc.vec.Vec (Option I128)) (used : Slice Bool)
    (amount : I128) (cursor : Nat) (hc : cursor < initial.length)
    (hframe : Frame initial current slackValue (slackExpected initial used amount cursor))
    (hflag : used.val[cursor]! = false) (habsent : current.val[cursor]! = none) :
    Frame initial current slackValue (slackExpected initial used amount (cursor+1)) := by
  apply frame_unchanged initial current slackValue _ _ hframe
  intro col hcol
  by_cases he : col = cursor
  · subst col
    have hold := (slackFrame_unprocessed initial current used amount cursor hc hframe).symm.trans habsent
    simp only [slackExpected, Nat.lt_add_one, hflag, and_self, ↓reduceIte, Nat.lt_irrefl, false_and, hold, slackValue, WithTop.top_add]
  · exact slackExpected_other initial used amount cursor col he

theorem slackFrame_some (initial current : alloc.vec.Vec (Option I128)) (used : Slice Bool)
    (amount : I128) (cursor : Usize) (old value : I128) (hc : cursor.val < initial.length)
    (hframe : Frame initial current slackValue (slackExpected initial used amount cursor.val))
    (hflag : used.val[cursor.val]! = false) (hpresent : current.val[cursor.val]! = some old)
    (hvalue : value.val = old.val-amount.val) :
    Frame initial (current.set cursor (some value)) slackValue (slackExpected initial used amount (cursor.val+1)) := by
  apply frame_set initial current slackValue _ _ cursor (some value) hframe hc
  · have hold := (slackFrame_unprocessed initial current used amount cursor.val hc hframe).symm.trans hpresent
    simp only [slackExpected, Nat.lt_add_one, hflag, and_self, ↓reduceIte, hold, slackValue]
    rw [hvalue, sub_eq_add_neg, WithTop.coe_add]
  · intro other _ hne
    exact slackExpected_other initial used amount cursor.val other hne

end SubtreeProofs.Rust.AssignmentAdjustmentInvariant

end
