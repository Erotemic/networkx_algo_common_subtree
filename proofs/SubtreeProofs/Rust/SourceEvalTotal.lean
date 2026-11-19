module

public import SubtreeProofs.Rust.SourceEvalSuccessRefinement

/-! Universal actual evaluator/native agreement for all finite native inputs and
warm tables, including overflow and early failure tables. Nesting fuel is chosen
from completed smaller calls and local helper depths; no global cost cap or
cache-soundness premise is assumed. Exact path costs remain in the composed run. -/

@[expose] public section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core Aeneas Aeneas.Std Result

theorem evaluate_total (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost, Evaluation fuel left right table result output cost := by
  cases hfind : MemoizedOrderedSolver.findResult table left right with
  | some result =>
    obtain ⟨lc, hr, _⟩ := cache_hit_source table left right result hfind (lookupDepth table left right) (by rfl)
    exact ⟨_, _, _, _, hr, cache_hit_native table left right result hfind⟩
  | none =>
    cases left with
    | Empty =>
      let f := lookupDepth table .Empty right + MemoSource.insertDepth .Empty right emptyWitness
      obtain ⟨lc, ci, hr, _⟩ := empty_source table .Empty right (Or.inl rfl) hfind f (by dsimp [f]; omega) (by dsimp [f]; omega)
      exact ⟨_, _, _, _, hr, empty_native table .Empty right (Or.inl rfl) hfind⟩
    | Pair lh lt =>
      cases right with
      | Empty =>
        let f := lookupDepth table (.Pair lh lt) .Empty + MemoSource.insertDepth (.Pair lh lt) .Empty emptyWitness
        obtain ⟨lc, ci, hr, _⟩ := empty_source table (.Pair lh lt) .Empty (Or.inr rfl) hfind f (by dsimp [f]; omega) (by dsimp [f]; omega)
        exact ⟨_, _, _, _, hr, empty_native table (.Pair lh lt) .Empty (Or.inr rfl) hfind⟩
      | Pair rh rt =>
        let depth := lookupDepth table (.Pair lh lt) (.Pair rh rt)
        let depthL := MemoSource.concatenateDepth lh lt
        let depthR := MemoSource.concatenateDepth rh rt
        obtain ⟨fh, heads, afterHeads, ch, hh⟩ := evaluate_total lh rh table
        cases heads with
        | none =>
          let f := fh + depth
          obtain ⟨lc, he, _⟩ := heads_failure_step table lh lt rh rt afterHeads f ch
            (by dsimp [f, depth]; omega) hfind (hh.extend (by dsimp [f]; omega))
          exact ⟨_, _, _, _, he⟩
        | some heads =>
          obtain ⟨ft, tails, afterTails, ct, ht⟩ := evaluate_total lt rt afterHeads
          cases tails with
          | none =>
            let f := fh + ft + depth
            obtain ⟨lc, he, _⟩ := tails_failure_step table lh lt rh rt heads afterHeads afterTails f ch ct
              (by dsimp [f, depth]; omega) hfind (hh.extend (by dsimp [f]; omega)) (ht.extend (by dsimp [f]; omega))
            exact ⟨_, _, _, _, he⟩
          | some tails =>
            cases ha : U32.checked_add heads.edges tails.edges with
            | none =>
              let f := fh + ft + depth
              obtain ⟨lc, he, _⟩ := subtotal_overflow_step table lh lt rh rt heads tails afterHeads afterTails f ch ct
                (by dsimp [f, depth]; omega) hfind (hh.extend (by dsimp [f]; omega)) (ht.extend (by dsimp [f]; omega)) ha
              exact ⟨_, _, _, _, he⟩
            | some subtotal =>
              cases hr : U32.checked_add subtotal 1#u32 with
              | none =>
                let f := fh + ft + depth
                obtain ⟨lc, he, _⟩ := root_overflow_step table lh lt rh rt heads tails subtotal afterHeads afterTails f ch ct
                  (by dsimp [f, depth]; omega) hfind (hh.extend (by dsimp [f]; omega)) (ht.extend (by dsimp [f]; omega)) ha hr
                exact ⟨_, _, _, _, he⟩
              | some total =>
                obtain ⟨fl, dropLeft, afterLeft, cl, hdl⟩ := evaluate_total (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails
                cases dropLeft with
                | none =>
                  let f := fh + ft + fl + depth + depthL
                  obtain ⟨lc, cc, he, _⟩ := left_failure_step table lh lt rh rt heads tails subtotal total
                    afterHeads afterTails afterLeft f ch ct cl (by dsimp [f, depth]; omega) (by dsimp [f, depthL]; omega)
                    hfind (hh.extend (by dsimp [f]; omega)) (ht.extend (by dsimp [f]; omega)) ha hr (hdl.extend (by dsimp [f]; omega))
                  exact ⟨_, _, _, _, he⟩
                | some dropLeft =>
                  obtain ⟨fr, dropRight, afterRight, cr, hdr⟩ := evaluate_total (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft
                  cases dropRight with
                  | none =>
                    let f := fh + ft + fl + fr + depth + depthL + depthR
                    obtain ⟨lc, cc, crc, he, _⟩ := right_failure_step table lh lt rh rt heads tails dropLeft subtotal total
                      afterHeads afterTails afterLeft afterRight f ch ct cl cr (by dsimp [f, depth]; omega)
                      (by dsimp [f, depthL]; omega) (by dsimp [f, depthR]; omega) hfind
                      (hh.extend (by dsimp [f]; omega)) (ht.extend (by dsimp [f]; omega)) ha hr
                      (hdl.extend (by dsimp [f]; omega)) (hdr.extend (by dsimp [f]; omega))
                    exact ⟨_, _, _, _, he⟩
                  | some dropRight =>
                    let result := OrderedSolver.selectResult (OrderedSolver.selectResult (matched heads tails total) dropLeft) dropRight
                    let depthI := MemoSource.insertDepth (.Pair lh lt) (.Pair rh rt) result
                    let f := fh + ft + fl + fr + depth + depthL + depthR + depthI
                    obtain ⟨lc, cc, crc, ci, he, _⟩ := success_step table lh lt rh rt heads tails dropLeft dropRight subtotal total
                      afterHeads afterTails afterLeft afterRight f ch ct cl cr (by dsimp [f, depth]; omega)
                      (by dsimp [f, depthL]; omega) (by dsimp [f, depthR]; omega) hfind
                      (hh.extend (by dsimp [f]; omega)) (ht.extend (by dsimp [f]; omega)) ha hr
                      (hdl.extend (by dsimp [f]; omega)) (hdr.extend (by dsimp [f]; omega)) (by change depthI ≤ f; dsimp [f]; omega)
                    exact ⟨_, _, _, _, he⟩
termination_by (OrderedSolver.toDyck left).semilength + (OrderedSolver.toDyck right).semilength
decreasing_by
  all_goals simp only [OrderedSolver.toDyck_appendWord, OrderedSolver.toDyck, DyckWord.semilength_add, DyckWord.semilength_nest]
  all_goals omega



theorem evaluate_refines (left right : BalancedWord) (table : MemoTable) (fuel : Nat)
    {value : Value} {cost : Cost}
    (hr : run Certificate.original.body fuel .evaluate
      [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] = some (value, cost)) :
    ∃ result output, value = encodeOutput result output ∧ Evaluation fuel left right table result output cost := by
  obtain ⟨other, result, output, current, he⟩ := evaluate_total left right table
  have hv := (run_unique _ hr he.source).1
  exact ⟨result, output, hv, ⟨by rwa [← hv], he.native⟩⟩

theorem Evaluation.unique {first last : Nat} {left right : BalancedWord} {table output₁ output₂ : MemoTable}
    {result₁ result₂ : Option CommonEmbedding} {cost₁ cost₂ : Cost}
    (h₁ : Evaluation first left right table result₁ output₁ cost₁)
    (h₂ : Evaluation last left right table result₂ output₂ cost₂) :
    result₁ = result₂ ∧ output₁ = output₂ ∧ cost₁ = cost₂ := by
  obtain ⟨hr, ht⟩ := Prod.mk.inj (Result.ok_injective (h₁.native.symm.trans h₂.native))
  exact ⟨hr, ht, (run_unique _ h₁.source h₂.source).2⟩

theorem evaluate_stable (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost, ∀ large, fuel ≤ large → Evaluation large left right table result output cost := by
  obtain ⟨fuel, result, output, cost, he⟩ := evaluate_total left right table
  exact ⟨fuel, result, output, cost, fun _ hf => he.extend hf⟩

theorem evaluate_source (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost,
      Certificate.executeSource Input.Program.source 512 fuel .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        .ok (some (encodeOutput result output, cost)) ∧
      memoized_common_embedding left right table = .ok (result, output) := by
  obtain ⟨fuel, result, output, cost, he⟩ := evaluate_total left right table
  exact ⟨fuel, result, output, cost, by rw [Certificate.original_execute, he.source], he.native⟩

theorem evaluate_consistent (left right : BalancedWord) (table : MemoTable)
    (hs : MemoizedOrderedSolver.TableSound table)
    (hl : (OrderedSolver.toDyck left).semilength < 2^32) (hr : (OrderedSolver.toDyck right).semilength < 2^32) :
    ∃ fuel result output cost, Evaluation fuel left right table (some result) output cost ∧
      MemoizedOrderedSolver.Consistent left right result ∧ MemoizedOrderedSolver.TableSound output ∧
      MemoizedOrderedSolver.numericMemo output =
        (Paper2004.OrderedTree.memoLcs (OrderedSolver.toDyck left) (OrderedSolver.toDyck right)
          (MemoizedOrderedSolver.numericMemo table)).table := by
  obtain ⟨fuel, result, output, cost, he⟩ := evaluate_total left right table
  obtain ⟨expected, after, hn, hc, ht, hm⟩ := MemoizedOrderedSolver.memoized_common_embedding_refines left right table hs hl hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective (he.native.symm.trans hn))
  exact ⟨fuel, expected, _, cost, he, hc, ht, hm⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
