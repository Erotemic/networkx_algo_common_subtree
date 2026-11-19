module

public import SubtreeProofs.Rust.Generated.LookupSourceProgram
public import SubtreeProofs.Rust.LookupSourceDeterminism

@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SubtreeProofs.Rust.LookupSource

open verified_ordered_core

attribute [lookup_source_simps] exec evalAction evalScrutinee evalRValue evalOperands
  evalOperand readPlace Env.set initialEnv selectBranch Action.weight RValue.weight
  Operand.weight Place.weight Scrutinee.weight Cost.plus entryEvents
  LookupEvents.Events.plus bind Option.bind

attribute [local lookup_source_simps] Program.body Program.copyWord Program.copyResult
  Program.compare Program.lookup

def wordHeight : BalancedWord → Nat
  | .Empty => 1
  | .Pair head tail => 1 + max (wordHeight head) (wordHeight tail)

theorem wordHeight_pos (word : BalancedWord) : 0 < wordHeight word := by
  cases word <;> simp [wordHeight]

theorem program_budget (function : Function) : (Program.body function).budget + 1 ≤ 256 := by
  cases function <;> decide

theorem program_source_bound {fuel : Nat} {function : Function} {args : List Value}
    {value : Value} {cost : Cost}
    (hr : run Program.body fuel function args = some (value, cost)) :
    cost.steps ≤ 256 * cost.events.units :=
  run_bound Program.body 256 (by decide) program_budget hr

theorem box_run (fuel : Nat) (hf : 0 < fuel) (value : Value) :
    run Program.body fuel .boxNew [value] =
      some (.boxed value, ⟨1, { allocations := 1 }⟩) := by
  cases fuel with
  | zero => omega
  | succ fuel => rw [run_succ]; rfl

theorem copy_empty (fuel : Nat) :
    run Program.body (fuel + 1) .copyWord [.reference (encodeWord .Empty)] =
      some (encodeWord .Empty, ⟨10, { copyNodes := 1 }⟩) := by
  rw [run_succ]
  simp only [lookup_source_simps, encodeWord]
  rfl

theorem copy_source (word : BalancedWord) (fuel : Nat) (hf : wordHeight word ≤ fuel) :
    ∃ cost, run Program.body fuel .copyWord [.reference (encodeWord word)] =
      some (encodeWord word, cost) ∧ cost.events = (LookupEvents.copy word).2 := by
  induction word generalizing fuel with
  | Empty =>
    cases fuel with
    | zero => simp [wordHeight] at hf
    | succ fuel => exact ⟨_, copy_empty fuel, rfl⟩
  | Pair head tail ihHead ihTail =>
    cases fuel with
    | zero => simp [wordHeight] at hf
    | succ fuel =>
      have hh : wordHeight head ≤ fuel := by simp only [wordHeight] at hf; omega
      have ht : wordHeight tail ≤ fuel := by simp only [wordHeight] at hf; omega
      have hp : 0 < fuel := lt_of_lt_of_le (wordHeight_pos head) hh
      obtain ⟨ch, heh, hch⟩ := ihHead fuel hh
      obtain ⟨ct, het, hct⟩ := ihTail fuel ht
      have hbox := fun value => box_run fuel hp value
      rw [run_succ]
      simp [lookup_source_simps, encodeWord, heh, het, hbox, LookupEvents.copy,
        LookupEvents.Events.plus, hch, hct]
      omega

theorem compare_source (first second : BalancedWord) (fuel : Nat)
    (hf : wordHeight first ≤ fuel) :
    ∃ cost, run Program.body fuel .compare [.reference (encodeWord first),
      .reference (encodeWord second)] = some (.boolean (LookupEvents.compare first second).1, cost) ∧
      cost.events = ⟨0, (LookupEvents.compare first second).2, 0, 0, 0⟩ := by
  induction first generalizing second fuel with
  | Empty =>
    cases fuel with
    | zero => simp [wordHeight] at hf
    | succ fuel =>
      cases second <;> rw [run_succ]
      all_goals simp [lookup_source_simps, encodeWord, LookupEvents.compare]
  | Pair head tail ihHead ihTail =>
    cases fuel with
    | zero => simp [wordHeight] at hf
    | succ fuel =>
      cases second with
      | Empty =>
        rw [run_succ]
        simp [lookup_source_simps, encodeWord, LookupEvents.compare]
      | Pair sh st =>
        have hh : wordHeight head ≤ fuel := by simp only [wordHeight] at hf; omega
        have ht : wordHeight tail ≤ fuel := by simp only [wordHeight] at hf; omega
        obtain ⟨ch, heh, hch⟩ := ihHead sh fuel hh
        obtain ⟨ct, het, hct⟩ := ihTail st fuel ht
        rw [run_succ]
        cases hb : (LookupEvents.compare head sh).1
        all_goals simp [lookup_source_simps, encodeWord, heh, het, LookupEvents.compare,
          hb, LookupEvents.Events.plus, hch, hct]
        all_goals omega

theorem copyResult_source (result : CommonEmbedding) (fuel : Nat)
    (hf : wordHeight result.word + 1 ≤ fuel) :
    ∃ cost, run Program.body fuel .copyResult [.reference (encodeResult result)] =
      some (encodeResult result, cost) ∧ cost.events = (LookupEvents.copyResult result).2 := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have hh : wordHeight result.word ≤ fuel := by omega
    obtain ⟨cw, hew, hcw⟩ := copy_source result.word fuel hh
    rw [run_succ]
    simp [lookup_source_simps, encodeResult, hew, LookupEvents.copyResult,
      LookupEvents.Events.plus, hcw]
    omega

/-- Sufficient call depth, including arbitrary cached witnesses. Neither sound
cache contents nor small stored keys are assumed by the first-hit API. -/
def tableHeight : MemoTable → Nat
  | .Empty => 1
  | .Entry entry rest => 1 + max (wordHeight entry.result.word + 1) (tableHeight rest)

def lookupDepth (table : MemoTable) (left right : BalancedWord) : Nat :=
  tableHeight table + max (wordHeight left) (wordHeight right) + 1

theorem lookup_source (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) :
    ∃ cost, run Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeOption (LookupEvents.lookup table left right).1, cost) ∧
      cost.events = (LookupEvents.lookup table left right).2 := by
  induction table generalizing fuel with
  | Empty =>
    cases fuel with
    | zero => simp [lookupDepth, tableHeight] at hf
    | succ fuel =>
      rw [run_succ]
      simp [lookup_source_simps, encodeTable, encodeOption, LookupEvents.lookup]
  | Entry entry rest ih =>
    cases fuel with
    | zero => simp [lookupDepth, tableHeight] at hf
    | succ fuel =>
      have hl : wordHeight left ≤ fuel := by simp only [lookupDepth, tableHeight] at hf; omega
      have hr : wordHeight right ≤ fuel := by simp only [lookupDepth, tableHeight] at hf; omega
      have hc : wordHeight entry.result.word + 1 ≤ fuel := by
        simp only [lookupDepth, tableHeight] at hf; omega
      have hs : lookupDepth rest left right ≤ fuel := by
        simp only [lookupDepth, tableHeight] at hf ⊢; omega
      obtain ⟨cl, hel, hcl⟩ := compare_source left entry.left fuel hl
      obtain ⟨cr, her, hcr⟩ := compare_source right entry.right fuel hr
      obtain ⟨cc, hec, hcc⟩ := copyResult_source entry.result fuel hc
      obtain ⟨cs, hes, hcs⟩ := ih fuel hs
      rw [run_succ]
      cases hbl : (LookupEvents.compare left entry.left).1
      all_goals cases hbr : (LookupEvents.compare right entry.right).1
      all_goals simp [lookup_source_simps, encodeTable, encodeOption, hel, her, hec, hes,
        LookupEvents.lookup, LookupEvents.copyResult_exact, hbl, hbr, hcl, hcr, hcc, hcs]
      all_goals omega

/-- Nonvacuous source-model lookup contract. Existence, first-hit value,
packet adequacy, and the complete instruction envelope are separate conjuncts. -/
theorem lookup_source_spec (table : MemoTable) (left right : BalancedWord)
    (hs : MemoizedOrderedSolver.TableSound table) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) :
    ∃ cost, run Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeOption (MemoizedOrderedSolver.findResult table left right), cost) ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧
      cost.steps ≤ 256 * (MemoizedOrderedSolver.memoLength table *
        (2 * (OrderedSolver.toDyck left).semilength +
          2 * (OrderedSolver.toDyck right).semilength + 3) +
        4 * min (OrderedSolver.toDyck left).semilength (OrderedSolver.toDyck right).semilength + 3) := by
  obtain ⟨cost, he, hc⟩ := lookup_source table left right fuel hf
  have hb := program_source_bound he
  have hp := LookupEvents.sound_unit_bound table left right hs
  rw [hc] at hb
  refine ⟨cost, ?_, hc, le_trans hb (Nat.mul_le_mul_left 256 hp)⟩
  simpa only [LookupEvents.lookup_value] using he

/-- Every completed run has the independent first-hit value and the same
packet counts, even when its fuel is smaller than the sufficient depth. -/
theorem lookup_source_all_runs (table : MemoTable) (left right : BalancedWord)
    {fuel : Nat} {value : Value} {cost : Cost}
    (hr : run Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (value, cost)) :
    value = encodeOption (MemoizedOrderedSolver.findResult table left right) ∧
      cost.events = (LookupEvents.lookup table left right).2 := by
  obtain ⟨reference, he, hc⟩ := lookup_source table left right (lookupDepth table left right) (le_refl _)
  obtain ⟨hv, hcost⟩ := run_unique Program.body hr he
  subst value
  subst cost
  exact ⟨by rw [LookupEvents.lookup_value], hc⟩

/-- The existing Aeneas theorem and the source-operation interpreter agree on
the independent result. Only the latter has a cost semantics. -/
theorem lookup_aeneas_value_agreement (table : MemoTable) (left right : BalancedWord)
    {fuel : Nat} {value : Value} {cost : Cost}
    (hr : run Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (value, cost)) :
    ∃ result, verified_ordered_core.memo_lookup table left right = .ok result ∧
      value = encodeOption result := by
  exact ⟨MemoizedOrderedSolver.findResult table left right,
    MemoizedOrderedSolver.memo_lookup_correct table left right,
    (lookup_source_all_runs table left right hr).1⟩

theorem lookup_all_runs_bound (table : MemoTable) (left right : BalancedWord)
    (hs : MemoizedOrderedSolver.TableSound table) {fuel : Nat} {value : Value} {cost : Cost}
    (hr : run Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (value, cost)) :
    cost.steps ≤ 256 * (MemoizedOrderedSolver.memoLength table *
      (2 * (OrderedSolver.toDyck left).semilength +
        2 * (OrderedSolver.toDyck right).semilength + 3) +
      4 * min (OrderedSolver.toDyck left).semilength (OrderedSolver.toDyck right).semilength + 3) := by
  have hb := program_source_bound hr
  rw [(lookup_source_all_runs table left right hr).2] at hb
  exact le_trans hb (Nat.mul_le_mul_left 256 (LookupEvents.sound_unit_bound table left right hs))

end SubtreeProofs.Rust.LookupSource
