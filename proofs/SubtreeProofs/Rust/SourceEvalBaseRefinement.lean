module

public import SubtreeProofs.Rust.SourceEvalBase
public import SubtreeProofs.Rust.SourceEvalBodyCertificate
public import SubtreeProofs.Rust.SourceEvalHelperRefinement

/-! Actual evaluator base executions, reusing native lookup/insertion contracts.
Warm tables and witnesses are arbitrary; no optimality or cache soundness is
assumed. Recursive pair/pair paths and addressed safety remain open. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core Aeneas Aeneas.Std Result

def hitRunCost (lookupCost : LookupSource.Cost) : Cost :=
  ⟨⟨67 + lookupCost.steps, lookupCost.events⟩, ⟨1, 0⟩, 1⟩

def emptyRunCost (left : BalancedWord) (lookupCost insertCost : LookupSource.Cost) : Cost :=
  ⟨⟨baseSteps left + 1 + lookupCost.steps + insertCost.steps, lookupCost.events.plus insertCost.events⟩,
    ⟨1, 0⟩, 1⟩

theorem source_of_exec (fuel : Nat) (args : List Value) (value : Value) (work : Cost)
    (he : exec (run Certificate.original.body fuel) body (initialState args) = some (.returned value, work)) :
    run Certificate.original.body (fuel + 1) .evaluate args = some (value, (Cost.entry .evaluate).plus work) := by
  rw [Legacy.run_ordinary Certificate.original.body fuel .evaluate args (by decide) (by decide), actual_body, he]
  rfl

theorem cache_hit_native (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding)
    (hfind : MemoizedOrderedSolver.findResult table left right = some result) :
    memoized_common_embedding left right table = .ok (some result, table) := by
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]

theorem cache_hit_source (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding)
    (hfind : MemoizedOrderedSolver.findResult table left right = some result) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) :
    ∃ lookupCost : LookupSource.Cost,
      run Certificate.original.body (fuel + 1) .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        some (encodeOutput (some result) table, hitRunCost lookupCost) ∧
      lookupCost.events = (LookupEvents.lookup table left right).2 := by
  obtain ⟨cost, hl, he⟩ := Helpers.lookup_source table left right fuel hf
  rw [LookupEvents.lookup_value, hfind] at hl
  have hb := cache_hit_exec (run Certificate.original.body fuel) table left right result (Legacy.costMap cost) hl
  have hr := source_of_exec fuel _ _ _ hb
  refine ⟨cost, ?_, he⟩
  have hc : (Cost.entry .evaluate).plus (hitCost (Legacy.costMap cost)) = hitRunCost cost := by
    simp [hitCost, hitRunCost, Legacy.costMap, Cost.entry, entryEvents, Cost.plus,
      LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus]
    omega
  exact hr.trans (congrArg (fun work => some (_, work)) hc)

theorem empty_native (table : MemoTable) (left right : BalancedWord)
    (hempty : left = .Empty ∨ right = .Empty)
    (hfind : MemoizedOrderedSolver.findResult table left right = none) :
    memoized_common_embedding left right table = .ok (some emptyWitness, .Entry ⟨left, right, emptyWitness⟩ table) := by
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  cases left with
  | Empty => simp only [MemoizedOrderedSolver.memo_insert_correct, bind_ok, emptyWitness]
  | Pair head tail =>
    rcases hempty with hbad | rfl
    · cases hbad
    · simp only [MemoizedOrderedSolver.memo_insert_correct, bind_ok, emptyWitness]

theorem empty_source (table : MemoTable) (left right : BalancedWord)
    (hempty : left = .Empty ∨ right = .Empty)
    (hfind : MemoizedOrderedSolver.findResult table left right = none) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (hi : MemoSource.insertDepth left right emptyWitness ≤ fuel) :
    ∃ lookupCost insertCost : LookupSource.Cost,
      run Certificate.original.body (fuel + 1) .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        some (encodeOutput (some emptyWitness) (.Entry ⟨left, right, emptyWitness⟩ table), emptyRunCost left lookupCost insertCost) ∧
      lookupCost.events = (LookupEvents.lookup table left right).2 ∧
      insertCost.events = MemoSource.insertEvents left right emptyWitness := by
  obtain ⟨lookupCost, hl, hel⟩ := Helpers.lookup_source table left right fuel hf
  rw [LookupEvents.lookup_value, hfind] at hl
  obtain ⟨insertCost, hins, hei⟩ := Helpers.insert_source table left right emptyWitness fuel hi
  have hb := empty_exec (run Certificate.original.body fuel) table left right hempty _
    (Legacy.costMap lookupCost) (Legacy.costMap insertCost) hl hins
  have hr := source_of_exec fuel _ _ _ hb
  refine ⟨lookupCost, insertCost, ?_, hel, hei⟩
  have hc : (Cost.entry .evaluate).plus (missCost (baseSteps left) (Legacy.costMap lookupCost) (Legacy.costMap insertCost)) =
      emptyRunCost left lookupCost insertCost := by
    simp [missCost, emptyRunCost, Legacy.costMap, Cost.entry, entryEvents, Cost.plus,
      LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus]
    omega
  exact hr.trans (congrArg (fun work => some (_, work)) hc)

theorem empty_source_total (table : MemoTable) (left right : BalancedWord)
    (hempty : left = .Empty ∨ right = .Empty) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (hi : MemoSource.insertDepth left right emptyWitness ≤ fuel) :
    ∃ result output cost,
      run Certificate.original.body (fuel + 1) .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        some (encodeOutput (some result) output, cost) ∧
      memoized_common_embedding left right table = .ok (some result, output) ∧
      cost.destroyed = ⟨1, 0⟩ ∧ cost.solverCalls = 1 := by
  cases hfind : MemoizedOrderedSolver.findResult table left right with
  | none =>
    obtain ⟨cl, ci, hr, _⟩ := empty_source table left right hempty hfind fuel hf hi
    exact ⟨_, _, _, hr, empty_native table left right hempty hfind, rfl, rfl⟩
  | some result =>
    obtain ⟨cl, hr, _⟩ := cache_hit_source table left right result hfind fuel hf
    exact ⟨_, _, _, hr, cache_hit_native table left right result hfind, rfl, rfl⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
