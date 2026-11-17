import SubtreeProofs.Rust.SourceEvalTotal

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource SubtreeProofs.Rust.LookupSource.Partial
open SubtreeProofs.Rust.SourceEval SubtreeProofs.Rust.SourceEval.Evaluator verified_ordered_core

private def one : BalancedWord := .Pair .Empty .Empty
private def two : BalancedWord := .Pair .Empty one
private def huge : CommonEmbedding := ⟨.Empty, 4294967295#u32⟩
private def zero : CommonEmbedding := ⟨.Empty, 0#u32⟩
private def rootCache : MemoTable := .Entry ⟨.Empty, .Empty, huge⟩ (.Entry ⟨one, one, zero⟩ .Empty)
private def sumCache : MemoTable := .Entry ⟨.Empty, .Empty, huge⟩ .Empty

private theorem root_eval : ∃ cost, Evaluation 21 two two rootCache none rootCache cost ∧
    cost.destroyed = ⟨13, 0⟩ ∧ cost.solverCalls = 3 := by
  obtain ⟨ch, hh, _⟩ := cache_hit_source rootCache .Empty .Empty huge (by rfl) 19 (by decide +kernel)
  obtain ⟨ct, ht, _⟩ := cache_hit_source rootCache one one zero (by rfl) 19 (by decide +kernel)
  have eh : Evaluation 20 .Empty .Empty rootCache (some huge) rootCache (hitRunCost ch) :=
    ⟨hh, cache_hit_native _ _ _ _ (by rfl)⟩
  have et : Evaluation 20 one one rootCache (some zero) rootCache (hitRunCost ct) :=
    ⟨ht, cache_hit_native _ _ _ _ (by rfl)⟩
  obtain ⟨lc, he, _⟩ := root_overflow_step rootCache .Empty one .Empty one huge zero huge.edges rootCache rootCache
    20 _ _ (by decide +kernel) (by rfl) eh et (by decide +kernel) (by decide +kernel)
  refine ⟨_, he, ?_, ?_⟩ <;>
    simp [SourceEval.Cost.entry, SourceEval.Cost.plus, SourceEval.Cost.local, SourceEval.entryEvents, pathCost, hitRunCost, Legacy.costMap,
      encodeResult, encodeWord, huge, zero, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]

-- The first addition succeeds at the exact u32 limit; adding the matched root
-- overflows and returns the exact warm table. No optimality premise is used.
example : ∃ cost, run Certificate.original.body 21 .evaluate
    [.reference (encodeWord two), .reference (encodeWord two), encodeTable rootCache] =
      some (encodeOutput none rootCache, cost) ∧ cost.destroyed = ⟨13, 0⟩ ∧ cost.solverCalls = 3 := by
  obtain ⟨c, he, hd, hc⟩ := root_eval
  exact ⟨c, he.source, hd, hc⟩

-- Overflow of the first addition is a distinct exit with the same exact table.
example : ∃ cost, Evaluation 21 one one sumCache none sumCache cost ∧
    cost.destroyed = ⟨13, 0⟩ ∧ cost.solverCalls = 3 := by
  obtain ⟨ch, hh, _⟩ := cache_hit_source sumCache .Empty .Empty huge (by rfl) 19 (by decide +kernel)
  have eh : Evaluation 20 .Empty .Empty sumCache (some huge) sumCache (hitRunCost ch) :=
    ⟨hh, cache_hit_native _ _ _ _ (by rfl)⟩
  obtain ⟨lc, he, _⟩ := subtotal_overflow_step sumCache .Empty .Empty .Empty .Empty huge huge sumCache sumCache
    20 _ _ (by decide +kernel) (by rfl) eh eh (by decide +kernel)
  refine ⟨_, he, ?_, ?_⟩ <;>
    simp [SourceEval.Cost.entry, SourceEval.Cost.plus, SourceEval.Cost.local, SourceEval.entryEvents, pathCost, hitRunCost, Legacy.costMap,
      encodeResult, encodeWord, huge, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]

-- A recursive failure must propagate the returned table through partial tuple
-- moves and cleanup. Increasing child fuel adds neither work nor calls.
example : ∃ cost, Evaluation 31 (.Pair two .Empty) (.Pair two .Empty) rootCache none rootCache cost ∧
    cost.destroyed = ⟨16, 0⟩ ∧ cost.solverCalls = 4 := by
  obtain ⟨childCost, child, hd, hc⟩ := root_eval
  obtain ⟨lc, parent, _⟩ := heads_failure_step rootCache two .Empty two .Empty rootCache 30 childCost
    (by decide +kernel) (by rfl) (child.extend (by decide +kernel))
  refine ⟨_, parent, ?_, ?_⟩ <;>
    simp [SourceEval.Cost.entry, SourceEval.Cost.plus, SourceEval.Cost.local, SourceEval.entryEvents, pathCost, Legacy.costMap, DropWork.plus, hd, hc]

-- Universal source reader/native consumer, including all success and failure
-- results for arbitrary finite input words and arbitrary warm caches.
example (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost,
      Certificate.executeSource SourceEval.Input.Program.source 512 fuel .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        .ok (some (encodeOutput result output, cost)) ∧
      memoized_common_embedding left right table = .ok (result, output) := evaluate_source left right table

example (left right : BalancedWord) (table : MemoTable) :
    ∃ fuel result output cost, ∀ large, fuel ≤ large → Evaluation large left right table result output cost :=
  evaluate_stable left right table

example (left right : BalancedWord) (hl : (OrderedSolver.toDyck left).semilength < 2^32)
    (hr : (OrderedSolver.toDyck right).semilength < 2^32) :
    ∃ fuel result output cost, Evaluation fuel left right .Empty (some result) output cost ∧
      MemoizedOrderedSolver.Consistent left right result ∧ MemoizedOrderedSolver.TableSound output ∧
      MemoizedOrderedSolver.numericMemo output =
        (SubtreeProofs.Paper2004.OrderedTree.memoLcs (OrderedSolver.toDyck left) (OrderedSolver.toDyck right) []).table :=
  evaluate_consistent left right .Empty trivial hl hr
