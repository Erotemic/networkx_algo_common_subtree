import SubtreeProofs.Rust.SourceEvalBaseRefinement

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource SubtreeProofs.Rust.SourceEval
open SubtreeProofs.Rust.SourceEval.Evaluator verified_ordered_core

private def cached : CommonEmbedding := ⟨.Pair .Empty .Empty, 4294967295#u32⟩
private def later : CommonEmbedding := ⟨.Empty, 99#u32⟩
private def warm : MemoTable := .Entry ⟨.Empty, .Empty, cached⟩ (.Entry ⟨.Empty, .Empty, later⟩ .Empty)

-- Empty queries may hit an unsound cache. Preserve its first witness and the
-- exact original table, including the duplicate-key suffix and maximal score.
example : ∃ cost, run Certificate.original.body 7 .evaluate
    [.reference (encodeWord .Empty), .reference (encodeWord .Empty), encodeTable warm] =
      some (encodeOutput (some cached) warm, cost) ∧ cost.destroyed = ⟨1, 0⟩ ∧ cost.solverCalls = 1 := by
  obtain ⟨cl, hr, _⟩ := cache_hit_source warm .Empty .Empty cached (by rfl) 6 (by decide +kernel)
  exact ⟨_, hr, rfl, rfl⟩

-- A cold empty/empty run prepends exactly one new entry and retains every
-- callee event. The local partial option consumes one visit and no Boxes.
example : ∃ cost, run Certificate.original.body 5 .evaluate
    [.reference (encodeWord .Empty), .reference (encodeWord .Empty), encodeTable .Empty] =
      some (encodeOutput (some emptyWitness) (.Entry ⟨.Empty, .Empty, emptyWitness⟩ .Empty), cost) ∧
    cost.work.events = ⟨1, 0, 3, 2, 1⟩ ∧ cost.destroyed = ⟨1, 0⟩ ∧ cost.solverCalls = 1 := by
  obtain ⟨cl, ci, hr, hel, hei⟩ := empty_source .Empty .Empty .Empty (Or.inl rfl) (by rfl) 4
    (by decide +kernel) (by decide +kernel)
  refine ⟨_, hr, ?_, rfl, rfl⟩
  simp only [emptyRunCost, hel, hei]
  rfl

-- Independent universal consumer: decode the actual input and retain native
-- agreement for all warm tables and either empty query, with sufficient depth.
example (table : MemoTable) (left right : BalancedWord) (hempty : left = .Empty ∨ right = .Empty) :
    ∃ fuel result output cost,
      Certificate.executeSource SourceEval.Input.Program.source 512 fuel .evaluate
        [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] =
        .ok (some (encodeOutput (some result) output, cost)) ∧
      memoized_common_embedding left right table = .ok (some result, output) ∧
      cost.destroyed.boxes = 0 ∧ cost.solverCalls = 1 := by
  let fuel := max (lookupDepth table left right) (MemoSource.insertDepth left right emptyWitness)
  obtain ⟨result, output, cost, hr, hn, hd, hc⟩ := empty_source_total table left right hempty fuel
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  refine ⟨fuel + 1, result, output, cost, ?_, hn, ?_, hc⟩
  · rw [Certificate.original_execute, hr]
  · rw [hd]
