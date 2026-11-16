module

public import SubtreeProofs.Rust.MemoizedOrderedSolver

/-!
# Structural operation packets for the owned memo lookup

This is the bounded event interpreter from campaign W02. It follows the two
short-circuit tests in the generated lookup, the head-before-tail comparison,
and the complete owned witness copy. Erasure is proved against actual extracted
functions. The event interpretation of source instructions remains an explicit
manual boundary: these theorems alone are not Rust runtime adequacy.

Each packet includes local discriminant/field/control/return work. Allocation
events count Box creations, not allocator steps or bytes. In particular, no
structural comparison or witness copy is charged as one constant-time operation.
-/

@[expose] public section

open Aeneas Aeneas.Std Result verified_ordered_core

namespace SubtreeProofs.Rust.LookupEvents

open OrderedSolver MemoizedOrderedSolver

/-- Calls/constructor visits, with owned-copy allocations kept separate. -/
structure Events where
  lookupNodes : Nat := 0
  compareNodes : Nat := 0
  copyNodes : Nat := 0
  allocations : Nat := 0
  resultCopies : Nat := 0
  deriving DecidableEq, Repr

def Events.plus (a b : Events) : Events :=
  ⟨a.lookupNodes + b.lookupNodes, a.compareNodes + b.compareNodes,
    a.copyNodes + b.copyNodes, a.allocations + b.allocations,
    a.resultCopies + b.resultCopies⟩

/-- Structural comparison visits only the tail after a successful head test. -/
def compare : BalancedWord → BalancedWord → Bool × Nat
  | .Empty, .Empty => (true, 1)
  | .Pair fh ft, .Pair sh st =>
    let head := compare fh sh
    if head.1 then
      let tail := compare ft st
      (tail.1, 1 + head.2 + tail.2)
    else (false, 1 + head.2)
  | _, _ => (false, 1)

theorem compare_value (first second : BalancedWord) :
    (compare first second).1 = decide (first = second) := by
  induction first generalizing second with
  | Empty => cases second <;> rfl
  | Pair head tail ihHead ihTail =>
    cases second with
    | Empty => rfl
    | Pair sh st =>
      simp only [compare, ihHead]
      by_cases hh : head = sh
      · subst sh
        simp [ihTail]
      · simp [hh]

/-- The query size bounds comparisons, with no bound on stored keys required. -/
theorem compare_bound (first second : BalancedWord) :
    (compare first second).2 ≤ 2 * (toDyck first).semilength + 1 := by
  induction first generalizing second with
  | Empty => cases second <;> simp [compare, toDyck]
  | Pair head tail ihHead ihTail =>
    cases second with
    | Empty => simp [compare, toDyck]
    | Pair sh st =>
      have hh := ihHead sh
      have ht := ihTail st
      simp only [compare]
      split <;> simp only [toDyck, DyckWord.semilength_add, DyckWord.semilength_nest]
      all_goals omega

theorem compare_self (word : BalancedWord) :
    compare word word = (true, 2 * (toDyck word).semilength + 1) := by
  induction word with
  | Empty => rfl
  | Pair head tail ihHead ihTail =>
    simp only [compare, ihHead, ihTail, ↓reduceIte, toDyck,
      DyckWord.semilength_add, DyckWord.semilength_nest, Prod.mk.injEq, true_and]
    omega

theorem compare_erases (first second : BalancedWord) :
    words_equal first second = .ok (compare first second).1 := by
  rw [words_equal_correct, compare_value]

/-- Each Pair copy allocates two Boxes; Empty copies still visit a constructor. -/
def copy : BalancedWord → BalancedWord × Events
  | .Empty => (.Empty, { copyNodes := 1 })
  | .Pair head tail =>
    let h := copy head
    let t := copy tail
    (.Pair h.1 t.1, (Events.plus h.2 t.2).plus { copyNodes := 1, allocations := 2 })

theorem copy_exact (word : BalancedWord) :
    copy word = (word, ⟨0, 0, 2 * (toDyck word).semilength + 1,
      2 * (toDyck word).semilength, 0⟩) := by
  induction word with
  | Empty => rfl
  | Pair head tail ihHead ihTail =>
    simp only [copy, ihHead, ihTail, Events.plus, toDyck,
      DyckWord.semilength_add, DyckWord.semilength_nest]
    congr 1; congr 1 <;> omega

theorem copy_erases (word : BalancedWord) : copy_word word = .ok (copy word).1 := by
  rw [copy_exact, copy_word_correct]

def copyResult (result : CommonEmbedding) : CommonEmbedding × Events :=
  let w := copy result.word
  ({ result with word := w.1 }, w.2.plus { resultCopies := 1 })

theorem copyResult_exact (result : CommonEmbedding) :
    copyResult result = (result, ⟨0, 0,
      2 * (toDyck result.word).semilength + 1,
      2 * (toDyck result.word).semilength, 1⟩) := by
  simp only [copyResult, copy_exact, Events.plus, Nat.add_zero, Nat.zero_add]

theorem copyResult_erases (result : CommonEmbedding) :
    copy_result result = .ok (copyResult result).1 := by
  rw [copyResult_exact, copy_result_correct]

/-- First-hit lookup on the actual owned table types, including duplicate keys. -/
def lookup : MemoTable → BalancedWord → BalancedWord → Option CommonEmbedding × Events
  | .Empty, _, _ => (none, { lookupNodes := 1 })
  | .Entry entry rest, left, right =>
    let l := compare left entry.left
    if l.1 then
      let r := compare right entry.right
      if r.1 then
        let result := copyResult entry.result
        (some result.1, result.2.plus { lookupNodes := 1, compareNodes := l.2 + r.2 })
      else
        let next := lookup rest left right
        (next.1, next.2.plus { lookupNodes := 1, compareNodes := l.2 + r.2 })
    else
      let next := lookup rest left right
      (next.1, next.2.plus { lookupNodes := 1, compareNodes := l.2 })

theorem lookup_value (table : MemoTable) (left right : BalancedWord) :
    (lookup table left right).1 = findResult table left right := by
  induction table generalizing left right with
  | Empty => rfl
  | Entry entry rest ih =>
    simp only [lookup, compare_value, copyResult_exact, findResult]
    by_cases hl : left = entry.left <;> by_cases hr : right = entry.right
    all_goals simp [hl, hr, ih]

theorem lookup_erases (table : MemoTable) (left right : BalancedWord) :
    memo_lookup table left right = .ok (lookup table left right).1 := by
  rw [memo_lookup_correct, lookup_value]

/-- Exact cost of the owned witness returned by first-hit lookup. -/
def outputEvents : Option CommonEmbedding → Events
  | none => {}
  | some result => ⟨0, 0, 2 * (toDyck result.word).semilength + 1,
      2 * (toDyck result.word).semilength, 1⟩

/-- Complete packet envelope, keeping output-dependent work visible even for
unsound tables with arbitrarily large cached witnesses. -/
theorem lookup_bound (table : MemoTable) (left right : BalancedWord) :
    let e := (lookup table left right).2
    let out := outputEvents (findResult table left right)
    e.lookupNodes ≤ memoLength table + 1 ∧
    e.compareNodes ≤ memoLength table *
      ((2 * (toDyck left).semilength + 1) + (2 * (toDyck right).semilength + 1)) ∧
    e.copyNodes = out.copyNodes ∧ e.allocations = out.allocations ∧
    e.resultCopies = out.resultCopies := by
  induction table with
  | Empty => simp [lookup, memoLength, findResult, outputEvents]
  | Entry entry rest ih =>
    have hlb := compare_bound left entry.left
    have hrb := compare_bound right entry.right
    dsimp only at ih
    simp only [lookup, compare_value]
    split
    · rename_i hl
      have hl' : left = entry.left := of_decide_eq_true hl
      split
      · rename_i hr
        have hr' : right = entry.right := of_decide_eq_true hr
        rw [findResult, ite_eq_left ⟨hl', hr'⟩]
        simp only [copyResult_exact, Events.plus, outputEvents, memoLength, Nat.add_mul,
          Nat.one_mul, Nat.add_zero, Nat.zero_add, and_true]
        omega
      · rename_i hr
        have hk : ¬(left = entry.left ∧ right = entry.right) := by
          intro h; exact hr (decide_eq_true h.2)
        rw [findResult, ite_eq_right hk]
        simp only [Events.plus, memoLength, Nat.add_mul]
        omega
    · rename_i hl
      have hk : ¬(left = entry.left ∧ right = entry.right) := by
        intro h; exact hl (decide_eq_true h.1)
      rw [findResult, ite_eq_right hk]
      simp only [Events.plus, memoLength, Nat.add_mul]
      omega

/-- Cache soundness, rather than key equality alone, bounds the copied witness
by the smaller query. No uniqueness premise is needed for first-hit lookup. -/
theorem sound_output_bound (table : MemoTable) (left right : BalancedWord)
    (hs : TableSound table) :
    let e := (lookup table left right).2
    let n := min (toDyck left).semilength (toDyck right).semilength
    e.copyNodes ≤ 2 * n + 1 ∧ e.allocations ≤ 2 * n ∧ e.resultCopies ≤ 1 := by
  have hb := lookup_bound table left right
  dsimp only at hb ⊢
  rw [hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2]
  cases hf : findResult table left right with
  | none => simp [outputEvents]
  | some result =>
    have hc := findResult_sound hs hf
    have hl : (toDyck result.word).semilength ≤ (toDyck left).semilength := by
      rw [hc.1]
      exact Paper2004.OrderedTree.dyckEmbeds_semilength_le
        (Paper2004.OrderedTree.paperCommon_sound _ _).1
    have hr : (toDyck result.word).semilength ≤ (toDyck right).semilength := by
      rw [hc.1]
      exact Paper2004.OrderedTree.dyckEmbeds_semilength_le
        (Paper2004.OrderedTree.paperCommon_sound _ _).2
    simp only [outputEvents]
    omega

/-- Unit prices are for the declared packets, not machine instructions. -/
def Events.units (e : Events) : Nat :=
  e.lookupNodes + e.compareNodes + e.copyNodes + e.allocations + e.resultCopies

theorem sound_unit_bound (table : MemoTable) (left right : BalancedWord)
    (hs : TableSound table) :
    (lookup table left right).2.units ≤
      memoLength table * (2 * (toDyck left).semilength +
        2 * (toDyck right).semilength + 3) +
      4 * min (toDyck left).semilength (toDyck right).semilength + 3 := by
  have hb := lookup_bound table left right
  have ho := sound_output_bound table left right hs
  dsimp only at hb ho
  unfold Events.units
  nlinarith [Nat.mul_add (memoLength table)
    (2 * (toDyck left).semilength + 1 + (2 * (toDyck right).semilength + 1)) 1]

/-- A first hit never inspects the suffix, regardless of its size or contents. -/
theorem first_hit_exact (left right : BalancedWord) (result : CommonEmbedding)
    (rest : MemoTable) :
    lookup (.Entry ⟨left, right, result⟩ rest) left right =
      (some result, ⟨1, (2 * (toDyck left).semilength + 1) +
        (2 * (toDyck right).semilength + 1),
        2 * (toDyck result.word).semilength + 1,
        2 * (toDyck result.word).semilength, 1⟩) := by
  simp only [lookup, compare_self, ↓reduceIte, copyResult_exact, Events.plus,
    Nat.add_zero, Nat.zero_add]

/-- An expensive stored right key is not compared after a left-key mismatch. -/
theorem left_mismatch (entry : MemoEntry) (rest : MemoTable) (left right : BalancedWord)
    (hl : left ≠ entry.left) :
    lookup (.Entry entry rest) left right =
      ((lookup rest left right).1,
        (lookup rest left right).2.plus
          { lookupNodes := 1, compareNodes := (compare left entry.left).2 }) := by
  simp only [lookup, compare_value, decide_eq_false hl, Bool.false_eq_true, ↓reduceIte]

/-- Repeating the lookup leaves its result unchanged but charges both scans.
The strictly positive extra lookup packet rules out the old exact trace. -/
def lookupTwice (table : MemoTable) (left right : BalancedWord) :
    Option CommonEmbedding × Events :=
  let first := lookup table left right
  let second := lookup table left right
  (second.1, first.2.plus second.2)

theorem lookup_positive (table : MemoTable) (left right : BalancedWord) :
    0 < (lookup table left right).2.lookupNodes := by
  cases table with
  | Empty => exact Nat.zero_lt_one
  | Entry entry rest =>
    simp only [lookup]
    split
    · split <;> simp [Events.plus]
    · simp [Events.plus]

theorem extra_scan_changes_cost (table : MemoTable) (left right : BalancedWord) :
    (lookupTwice table left right).1 = (lookup table left right).1 ∧
    (lookup table left right).2.lookupNodes < (lookupTwice table left right).2.lookupNodes := by
  have hp := lookup_positive table left right
  simp only [lookupTwice, Events.plus]
  exact ⟨trivial, by omega⟩

end SubtreeProofs.Rust.LookupEvents
