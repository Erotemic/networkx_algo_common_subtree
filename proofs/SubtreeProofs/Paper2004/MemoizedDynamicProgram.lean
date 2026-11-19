module

public import SubtreeProofs.Paper2004.DynamicProgram
public import SubtreeProofs.Paper2004.TreeStateBounds
public import Mathlib.Data.Finset.Prod

/-!
# Memoized balanced-embedding scores

The maintained reference memo table is an association list. Lookup therefore
has linear comparison cost; it is not claimed to implement constant-time
hashing. Correctness is proved for this actual computation before counting its
misses, table operations and representation-dependent costs.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

abbrev MemoKey := DyckWord × DyckWord
abbrev MemoTable := List (MemoKey × Nat)

/-- Association-list lookup with structural equality on the two words. -/
def memoLookup (key : MemoKey) : MemoTable → Option Nat
  | [] => none
  | (stored, value) :: rest => if key = stored then some value else memoLookup key rest


/-- Lookup and its exact number of key comparisons, computed together. -/
def memoFind (key : MemoKey) : MemoTable → Option Nat × Nat
  | [] => (none, 0)
  | (stored, value) :: rest =>
    if key = stored then (some value, 1) else
      let result := memoFind key rest
      (result.1, result.2 + 1)

@[simp] theorem memoFind_value (key : MemoKey) (table : MemoTable) :
    (memoFind key table).1 = memoLookup key table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    simp only [memoFind, memoLookup]
    split <;> simp only [ih]

theorem memoFind_comparisons (key : MemoKey) (table : MemoTable) :
    (memoFind key table).2 ≤ table.length := by
  induction table with
  | nil => simp [memoFind]
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    simp only [memoFind]
    split <;> simp only [List.length_cons] <;> omega

/-- Table correctness is stated against the separately specified recurrence. -/
def MemoSound (table : MemoTable) : Prop :=
  ∀ entry ∈ table, entry.2 = paperLcs entry.1.1 entry.1.2

/-- Reading a sound memo table yields the right score. -/
theorem memoLookup_sound {table : MemoTable} (h : MemoSound table)
    (left right : DyckWord) {value : Nat} (hlookup : memoLookup (left, right) table = some value) :
    value = paperLcs left right := by
  induction table with
  | nil => simp [memoLookup] at hlookup
  | cons entry rest ih =>
    rcases entry with ⟨⟨a,b⟩,v⟩
    simp only [memoLookup] at hlookup
    split at hlookup
    · rename_i hkey
      cases hkey
      cases hlookup
      exact h _ List.mem_cons_self
    · exact ih (fun entry he => h entry (List.mem_cons_of_mem _ he)) hlookup

/-- Adding a certified value preserves memo correctness. -/
theorem MemoSound.cons {table : MemoTable} (h : MemoSound table)
    {left right : DyckWord} {value : Nat} (hv : value = paperLcs left right) :
    MemoSound (((left, right), value) :: table) := by
  intro entry he
  rcases List.mem_cons.mp he with rfl | he
  · exact hv
  · exact h entry he

/-- Instrumentation follows the actual evaluation: one call per lookup and
one miss per insertion. The counters exclude structural word-comparison cost. -/
structure MemoRun where
  value : Nat
  table : MemoTable
  calls : Nat
  misses : Nat
  comparisons : Nat

/-- The actual memoized numerical recurrence, threading every updated table. -/
def memoLcs (left right : DyckWord) (table : MemoTable) : MemoRun :=
  let found := memoFind (left, right) table
  match found.1 with
  | some value => ⟨value, table, 1, 0, found.2⟩
  | none =>
    if _hl : left = 0 then ⟨0, ((left, right), 0) :: table, 1, 1, found.2⟩ else
    if _hr : right = 0 then ⟨0, ((left, right), 0) :: table, 1, 1, found.2⟩ else
      let heads := memoLcs left.insidePart right.insidePart table
      let tails := memoLcs left.outsidePart right.outsidePart heads.table
      let dropLeft := memoLcs (left.insidePart + left.outsidePart) right tails.table
      let dropRight := memoLcs left (right.insidePart + right.outsidePart) dropLeft.table
      let value := max (max (heads.value + tails.value + 1) dropLeft.value) dropRight.value
      ⟨value, ((left, right), value) :: dropRight.table,
        heads.calls + tails.calls + dropLeft.calls + dropRight.calls + 1,
        heads.misses + tails.misses + dropLeft.misses + dropRight.misses + 1,
        found.2 + heads.comparisons + tails.comparisons + dropLeft.comparisons + dropRight.comparisons⟩
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- Memoization computes the same recurrence and preserves every stored value. -/
theorem memoLcs_correct (left right : DyckWord) (table : MemoTable) (hs : MemoSound table) :
    (memoLcs left right table).value = paperLcs left right ∧ MemoSound (memoLcs left right table).table := by
  rw [memoLcs]
  simp only [memoFind_value]
  split
  · rename_i value hlookup
    exact ⟨memoLookup_sound hs left right hlookup, hs⟩
  · split
    · rename_i hl
      have hv : 0 = paperLcs left right := by rw [paperLcs]; simp [hl]
      exact ⟨hv, hs.cons hv⟩
    · rename_i hl
      split
      · rename_i hr
        have hv : 0 = paperLcs left right := by rw [paperLcs]; simp [hl, hr]
        exact ⟨hv, hs.cons hv⟩
      · rename_i hr
        have hh := memoLcs_correct left.insidePart right.insidePart table hs
        have ht := memoLcs_correct left.outsidePart right.outsidePart _ hh.2
        have hdl := memoLcs_correct (left.insidePart + left.outsidePart) right _ ht.2
        have hdr := memoLcs_correct left (right.insidePart + right.outsidePart) _ hdl.2
        have hv : max (max ((memoLcs left.insidePart right.insidePart table).value +
              (memoLcs left.outsidePart right.outsidePart (memoLcs left.insidePart right.insidePart table).table).value + 1)
            (memoLcs (left.insidePart + left.outsidePart) right
              (memoLcs left.outsidePart right.outsidePart (memoLcs left.insidePart right.insidePart table).table).table).value)
            (memoLcs left (right.insidePart + right.outsidePart)
              (memoLcs (left.insidePart + left.outsidePart) right
                (memoLcs left.outsidePart right.outsidePart (memoLcs left.insidePart right.insidePart table).table).table).table).value =
            paperLcs left right := by
          rw [hh.1, ht.1, hdl.1, hdr.1]
          conv_rhs => rw [paperLcs]
          simp only [hl, hr, ↓reduceDIte]
        exact ⟨hv, hdr.2.cons hv⟩
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega


/-- A cache hit preserves the table exactly. -/
theorem memoLcs_hit_table (left right : DyckWord) (table : MemoTable) (value : Nat)
    (h : memoLookup (left,right) table = some value) : (memoLcs left right table).table = table := by
  rw [memoLcs]
  simp only [memoFind_value, h]

/-- On a nonempty miss, the final insertion has the independently proved
recurrence value and follows the four threaded child computations. -/
theorem memoLcs_miss_table (left right : DyckWord) (table : MemoTable) (hs : MemoSound table)
    (h : memoLookup (left,right) table = none) (hl : left ≠ 0) (hr : right ≠ 0) :
    (memoLcs left right table).table = ((left,right), paperLcs left right) ::
      (memoLcs left (right.insidePart + right.outsidePart)
        (memoLcs (left.insidePart + left.outsidePart) right
          (memoLcs left.outsidePart right.outsidePart
            (memoLcs left.insidePart right.insidePart table).table).table).table).table := by
  have hv := (memoLcs_correct left right table hs).1
  rw [memoLcs] at hv ⊢
  simp only [memoFind_value, h, hl, hr, ↓reduceDIte] at hv ⊢
  rw [hv]

/-- Empty-table execution equals the independent maximum common balanced score. -/
theorem memoLcs_optimum (left right : DyckWord) :
    (∃ candidate, CommonBalanced candidate left right ∧
      candidate.semilength = (memoLcs left right []).value) ∧
      ∀ candidate, CommonBalanced candidate left right →
        candidate.semilength ≤ (memoLcs left right []).value := by
  have hsound : MemoSound [] := by intro entry he; simp at he
  rw [(memoLcs_correct left right [] hsound).1]
  exact paperLcs_optimum left right

/-- Each miss adds exactly one entry, and at most four recursive lookups are
caused by a miss. These counts belong to the actual threaded computation. -/
theorem memoLcs_counts (left right : DyckWord) (table : MemoTable) :
    table.length + (memoLcs left right table).misses = (memoLcs left right table).table.length ∧
      (memoLcs left right table).calls ≤ 4 * (memoLcs left right table).misses + 1 := by
  rw [memoLcs]
  simp only [memoFind_value]
  split
  · simp
  · split
    · simp
    · rename_i hl
      split
      · simp
      · rename_i hr
        have hh := memoLcs_counts left.insidePart right.insidePart table
        have ht := memoLcs_counts left.outsidePart right.outsidePart
          (memoLcs left.insidePart right.insidePart table).table
        have hdl := memoLcs_counts (left.insidePart + left.outsidePart) right
          (memoLcs left.outsidePart right.outsidePart
            (memoLcs left.insidePart right.insidePart table).table).table
        have hdr := memoLcs_counts left (right.insidePart + right.outsidePart)
          (memoLcs (left.insidePart + left.outsidePart) right
            (memoLcs left.outsidePart right.outsidePart
              (memoLcs left.insidePart right.insidePart table).table).table).table
        constructor <;> dsimp only <;> (try simp only [List.length_cons]) <;> omega
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- Actual legal memo keys from the two decomposition families. -/
def MemoDomain (left right : DyckWord) (key : MemoKey) : Prop :=
  key.1 ∈ BalancedDecomposition.states left ∧ key.2 ∈ BalancedDecomposition.states right

/-- Domain inclusion is inherited from decomposition-state inclusion. -/
theorem MemoDomain.trans {left right first second : DyckWord} {key : MemoKey}
    (inner : MemoDomain first second key) (outer : MemoDomain left right (first, second)) :
    MemoDomain left right key :=
  ⟨BalancedDecomposition.states_trans outer.1 inner.1,
    BalancedDecomposition.states_trans outer.2 inner.2⟩

/-- Memoization only adds keys from the actual product of decomposition families. -/
theorem memoLcs_new_keys (left right : DyckWord) (table : MemoTable) :
    ∀ entry ∈ (memoLcs left right table).table,
      entry ∈ table ∨ MemoDomain left right entry.1 := by
  rw [memoLcs]
  simp only [memoFind_value]
  split
  · intro entry he
    exact Or.inl he
  · split
    · intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr ⟨BalancedDecomposition.mem_states_self _, BalancedDecomposition.mem_states_self _⟩
      · exact Or.inl he
    · rename_i hl
      split
      · intro entry he
        rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr ⟨BalancedDecomposition.mem_states_self _, BalancedDecomposition.mem_states_self _⟩
        · exact Or.inl he
      · rename_i hr
        have hh := memoLcs_new_keys left.insidePart right.insidePart table
        have ht := memoLcs_new_keys left.outsidePart right.outsidePart
          (memoLcs left.insidePart right.insidePart table).table
        have hdl := memoLcs_new_keys (left.insidePart + left.outsidePart) right
          (memoLcs left.outsidePart right.outsidePart
            (memoLcs left.insidePart right.insidePart table).table).table
        have hdr := memoLcs_new_keys left (right.insidePart + right.outsidePart)
          (memoLcs (left.insidePart + left.outsidePart) right
            (memoLcs left.outsidePart right.outsidePart
              (memoLcs left.insidePart right.insidePart table).table).table).table
        have hleft := BalancedDecomposition.states_closed (BalancedDecomposition.mem_states_self left) hl
        have hright := BalancedDecomposition.states_closed (BalancedDecomposition.mem_states_self right) hr
        intro entry he
        rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr ⟨BalancedDecomposition.mem_states_self _, BalancedDecomposition.mem_states_self _⟩
        · rcases hdr entry he with he | hnew
          · rcases hdl entry he with he | hnew
            · rcases ht entry he with he | hnew
              · rcases hh entry he with he | hnew
                · exact Or.inl he
                · exact Or.inr (hnew.trans ⟨hleft.1, hright.1⟩)
              · exact Or.inr (hnew.trans ⟨hleft.2.1, hright.2.1⟩)
            · exact Or.inr (hnew.trans ⟨hleft.2.2, BalancedDecomposition.mem_states_self _⟩)
          · exact Or.inr (hnew.trans ⟨BalancedDecomposition.mem_states_self _, hright.2.2⟩)
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- An association-list miss is exactly absence of that key. -/
theorem memoLookup_none_iff (key : MemoKey) (table : MemoTable) :
    memoLookup key table = none ↔ key ∉ table.map Prod.fst := by
  induction table with
  | nil => simp [memoLookup]
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    by_cases hk : key = stored
    · simp [memoLookup, hk]
    · simp [memoLookup, hk, ih]

/-- A smaller recursive state cannot introduce an absent larger key. -/
theorem memoLcs_preserves_fresh (left right : DyckWord) (table : MemoTable) (key : MemoKey)
    (hrank : left.semilength + right.semilength < key.1.semilength + key.2.semilength)
    (hfresh : memoLookup key table = none) :
    memoLookup key (memoLcs left right table).table = none := by
  apply (memoLookup_none_iff _ _).mpr
  intro hmem
  obtain ⟨entry, he, hkey⟩ := List.mem_map.mp hmem
  rcases memoLcs_new_keys left right table entry he with hold | hnew
  · apply (memoLookup_none_iff _ _).mp hfresh
    exact List.mem_map.mpr ⟨entry, hold, hkey⟩
  · unfold MemoDomain at hnew
    rw [hkey] at hnew
    have hl := BalancedDecomposition.states_semilength_le hnew.1
    have hr := BalancedDecomposition.states_semilength_le hnew.2
    omega

/-- No state is inserted twice. Recursive calls have smaller rank than the
current key, so they cannot invalidate the miss which preceded them. -/
theorem memoLcs_nodup (left right : DyckWord) (table : MemoTable)
    (hunique : (table.map Prod.fst).Nodup) :
    ((memoLcs left right table).table.map Prod.fst).Nodup := by
  rw [memoLcs]
  simp only [memoFind_value]
  split
  · exact hunique
  · rename_i hlookup
    split
    · exact List.nodup_cons.mpr ⟨(memoLookup_none_iff _ _).mp hlookup, hunique⟩
    · rename_i hl
      split
      · exact List.nodup_cons.mpr ⟨(memoLookup_none_iff _ _).mp hlookup, hunique⟩
      · rename_i hr
        have hcL := BalancedDecomposition.contracted_semilength hl
        have hcR := BalancedDecomposition.contracted_semilength hr
        simp only [DyckWord.semilength_add] at hcL hcR
        have hh := memoLcs_nodup left.insidePart right.insidePart table hunique
        have ht := memoLcs_nodup left.outsidePart right.outsidePart _ hh
        have hdl := memoLcs_nodup (left.insidePart + left.outsidePart) right _ ht
        have hdr := memoLcs_nodup left (right.insidePart + right.outsidePart) _ hdl
        have fh := memoLcs_preserves_fresh left.insidePart right.insidePart table
          (left, right) (by dsimp; omega) hlookup
        have ft := memoLcs_preserves_fresh left.outsidePart right.outsidePart
          (memoLcs left.insidePart right.insidePart table).table
          (left, right) (by dsimp; omega) fh
        have fdl := memoLcs_preserves_fresh (left.insidePart + left.outsidePart) right
          (memoLcs left.outsidePart right.outsidePart
            (memoLcs left.insidePart right.insidePart table).table).table
          (left, right) (by simp only [DyckWord.semilength_add]; omega) ft
        have fdr := memoLcs_preserves_fresh left (right.insidePart + right.outsidePart)
          (memoLcs (left.insidePart + left.outsidePart) right
            (memoLcs left.outsidePart right.outsidePart
              (memoLcs left.insidePart right.insidePart table).table).table).table
          (left, right) (by simp only [DyckWord.semilength_add]; omega) fdl
        exact List.nodup_cons.mpr ⟨(memoLookup_none_iff _ _).mp fdr, hdr⟩
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- Table size is bounded by the real finite product domain; no free state-count
hypothesis or memo-evaluation hypothesis appears in this result. -/
theorem memoLcs_table_bound (left right : DyckWord) :
    (memoLcs left right []).table.length ≤
      (BalancedDecomposition.states left).card * (BalancedDecomposition.states right).card := by
  have hnodup := memoLcs_nodup left right [] (by simp)
  have hsub : ((memoLcs left right []).table.map Prod.fst).toFinset ⊆
      (BalancedDecomposition.states left).product (BalancedDecomposition.states right) := by
    intro key hk
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    rcases memoLcs_new_keys left right [] entry he with hold | hnew
    · simp at hold
    · exact Finset.mem_product.mpr hnew
  have hc := Finset.card_le_card hsub
  have hp : ((BalancedDecomposition.states left).product (BalancedDecomposition.states right)).card =
      (BalancedDecomposition.states left).card * (BalancedDecomposition.states right).card :=
    Finset.card_product _ _
  rw [hp] at hc
  simpa only [List.toFinset_card_of_nodup hnodup, List.length_map] using hc

/-- A finite bound on actual lookup invocations and insertions. The association
list implementation separately pays for the comparisons within each lookup. -/
theorem memoLcs_operation_bound (left right : DyckWord) :
    (memoLcs left right []).misses ≤
        (BalancedDecomposition.states left).card * (BalancedDecomposition.states right).card ∧
      (memoLcs left right []).calls ≤
        4 * ((BalancedDecomposition.states left).card * (BalancedDecomposition.states right).card) + 1 := by
  have hc := memoLcs_counts left right []
  have hs := memoLcs_table_bound left right
  simp only [List.length_nil, zero_add] at hc
  constructor <;> omega

/-- Paper-parameter operation count, now tied to the actual memoized execution.
This counts table operations, not wall-clock runtime or word representation work. -/
theorem memoLcs_tree_operation_bound (left right : OrderedTree) :
    (memoLcs left.encodeDyck right.encodeDyck []).calls ≤
      4 * ((left.edgeCount * (min left.treeDepth left.leafCount + 1) + 1) *
        (right.edgeCount * (min right.treeDepth right.leafCount + 1) + 1)) + 1 := by
  have hl := decomposition_card_bound left
  have hr := decomposition_card_bound right
  have hm := Nat.mul_le_mul hl hr
  have hc := (memoLcs_operation_bound left.encodeDyck right.encodeDyck).2
  omega

/-- Exact association-list execution makes at most `calls * final table size`
key comparisons. This accounts for the list table instead of postulating O(1) lookup. -/
theorem memoLcs_comparison_bound (left right : DyckWord) (table : MemoTable) :
    (memoLcs left right table).comparisons ≤
      (memoLcs left right table).calls * (memoLcs left right table).table.length := by
  rw [memoLcs]
  simp only [memoFind_value]
  split
  · simpa only [one_mul] using memoFind_comparisons (left, right) table
  · split
    · have hf := memoFind_comparisons (left, right) table
      dsimp only
      simp only [List.length_cons, one_mul]
      omega
    · rename_i hl
      split
      · have hf := memoFind_comparisons (left, right) table
        dsimp only
        simp only [List.length_cons, one_mul]
        omega
      · rename_i hr
        let heads := memoLcs left.insidePart right.insidePart table
        let tails := memoLcs left.outsidePart right.outsidePart heads.table
        let dl := memoLcs (left.insidePart + left.outsidePart) right tails.table
        let dr := memoLcs left (right.insidePart + right.outsidePart) dl.table
        have hh := memoLcs_comparison_bound left.insidePart right.insidePart table
        have ht := memoLcs_comparison_bound left.outsidePart right.outsidePart heads.table
        have hdl := memoLcs_comparison_bound (left.insidePart + left.outsidePart) right tails.table
        have hdr := memoLcs_comparison_bound left (right.insidePart + right.outsidePart) dl.table
        change heads.comparisons ≤ heads.calls * heads.table.length at hh
        change tails.comparisons ≤ tails.calls * tails.table.length at ht
        change dl.comparisons ≤ dl.calls * dl.table.length at hdl
        change dr.comparisons ≤ dr.calls * dr.table.length at hdr
        have nh := (memoLcs_counts left.insidePart right.insidePart table).1
        have nt := (memoLcs_counts left.outsidePart right.outsidePart heads.table).1
        have ndl := (memoLcs_counts (left.insidePart + left.outsidePart) right tails.table).1
        have ndr := (memoLcs_counts left (right.insidePart + right.outsidePart) dl.table).1
        change table.length + heads.misses = heads.table.length at nh
        change heads.table.length + tails.misses = tails.table.length at nt
        change tails.table.length + dl.misses = dl.table.length at ndl
        change dl.table.length + dr.misses = dr.table.length at ndr
        have fh := Nat.mul_le_mul_left heads.calls (show heads.table.length ≤ dr.table.length+1 by omega)
        have ft := Nat.mul_le_mul_left tails.calls (show tails.table.length ≤ dr.table.length+1 by omega)
        have fdl := Nat.mul_le_mul_left dl.calls (show dl.table.length ≤ dr.table.length+1 by omega)
        have fdr := Nat.mul_le_mul_left dr.calls (show dr.table.length ≤ dr.table.length+1 by omega)
        have ff := memoFind_comparisons (left, right) table
        change (memoFind (left,right) table).2 + heads.comparisons + tails.comparisons +
          dl.comparisons + dr.comparisons ≤
          (heads.calls + tails.calls + dl.calls + dr.calls + 1) * (dr.table.length + 1)
        nlinarith
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- Concrete comparison work of the association-list reference is quadratic
in the product state count, rather than the paper's constant-time table model. -/
theorem memoLcs_comparison_state_bound (left right : DyckWord) :
    (memoLcs left right []).comparisons ≤
      (4 * ((BalancedDecomposition.states left).card * (BalancedDecomposition.states right).card) + 1) *
        ((BalancedDecomposition.states left).card * (BalancedDecomposition.states right).card) := by
  exact (memoLcs_comparison_bound left right []).trans
    (Nat.mul_le_mul (memoLcs_operation_bound left right).2 (memoLcs_table_bound left right))

end SubtreeProofs.Paper2004.OrderedTree

end
