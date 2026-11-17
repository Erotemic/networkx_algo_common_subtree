module

public import SubtreeProofs.Rust.SourceEvalContractFailures
public import SubtreeProofs.Rust.SourceEvalBaseRefinement
public import SubtreeProofs.Rust.SourceEvalDeterminism

/-! Source/native recursive composition rules. Every recursive premise is a
completed smaller call with its actual returned table and full cost, not a
specification assumed for the parent. Whole-run induction remains separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core Aeneas Aeneas.Std Result

structure Evaluation (fuel : Nat) (left right : BalancedWord) (table : MemoTable)
    (result : Option CommonEmbedding) (output : MemoTable) (cost : Cost) : Prop where
  source : run Certificate.original.body fuel .evaluate
    [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] = some (encodeOutput result output, cost)
  native : memoized_common_embedding left right table = .ok (result, output)

theorem Evaluation.extend {small large : Nat} {left right : BalancedWord} {table output : MemoTable}
    {result : Option CommonEmbedding} {cost : Cost} (h : Evaluation small left right table result output cost)
    (hf : small ≤ large) : Evaluation large left right table result output cost :=
  ⟨run_extends _ hf h.source, h.native⟩

theorem lookup_none (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (hfind : MemoizedOrderedSolver.findResult table left right = none) :
    ∃ cost : LookupSource.Cost, run Certificate.original.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
      some (encodeOption none, Legacy.costMap cost) ∧ cost.events = (LookupEvents.lookup table left right).2 := by
  obtain ⟨cost, hr, he⟩ := Helpers.lookup_source table left right fuel hf
  rw [LookupEvents.lookup_value, hfind] at hr
  exact ⟨cost, hr, he⟩

theorem checked_add_source (fuel : Nat) (hf : 0 < fuel) (left right : U32) :
    run Certificate.original.body fuel .checkedAdd [.number left.val, .number right.val] =
      some (encodeNumberOption ((U32.checked_add left right).map (fun value => value.val)), Cost.entry .checkedAdd) := by
  cases fuel with
  | zero => omega
  | succ fuel => exact run_checkedAdd _ fuel left right

theorem heads_failure_step (table : MemoTable) (lh lt rh rt : BalancedWord) (output : MemoTable)
    (fuel : Nat) (headsCost : Cost)
    (hf : lookupDepth table (.Pair lh lt) (.Pair rh rt) ≤ fuel)
    (hfind : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (hh : Evaluation fuel lh rh table none output headsCost) :
    ∃ lookupCost : LookupSource.Cost,
      Evaluation (fuel + 1) (.Pair lh lt) (.Pair rh rt) table none output
        ((Cost.entry .evaluate).plus (pathCost 156 ⟨3, 0⟩ [Legacy.costMap lookupCost, headsCost])) ∧
      lookupCost.events = (LookupEvents.lookup table (.Pair lh lt) (.Pair rh rt)).2 := by
  obtain ⟨lc, hl, he⟩ := lookup_none table _ _ fuel hf hfind
  refine ⟨lc, ⟨source_of_exec fuel _ _ _ (heads_failure_exec _ table lh lt rh rt output _ _ hl hh.source), ?_⟩, he⟩
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  simp only [hh.native, bind_ok, uncurry_apply_pair]

theorem tails_failure_step (table : MemoTable) (lh lt rh rt : BalancedWord) (heads : CommonEmbedding)
    (afterHeads output : MemoTable) (fuel : Nat) (headsCost tailsCost : Cost)
    (hf : lookupDepth table (.Pair lh lt) (.Pair rh rt) ≤ fuel)
    (hfind : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (hh : Evaluation fuel lh rh table (some heads) afterHeads headsCost)
    (ht : Evaluation fuel lt rt afterHeads none output tailsCost) :
    ∃ lookupCost : LookupSource.Cost,
      Evaluation (fuel + 1) (.Pair lh lt) (.Pair rh rt) table none output
        ((Cost.entry .evaluate).plus (pathCost 208 ((Slot.ofValue (encodeResult heads)).dropWork.plus ⟨5, 0⟩)
          [Legacy.costMap lookupCost, headsCost, tailsCost])) ∧
      lookupCost.events = (LookupEvents.lookup table (.Pair lh lt) (.Pair rh rt)).2 := by
  obtain ⟨lc, hl, he⟩ := lookup_none table _ _ fuel hf hfind
  refine ⟨lc, ⟨source_of_exec fuel _ _ _ (tails_failure_exec _ table lh lt rh rt heads afterHeads output _ _ _ hl hh.source ht.source), ?_⟩, he⟩
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  simp only [hh.native, ht.native, bind_ok, uncurry_apply_pair]

theorem subtotal_overflow_step (table : MemoTable) (lh lt rh rt : BalancedWord) (heads tails : CommonEmbedding)
    (afterHeads output : MemoTable) (fuel : Nat) (headsCost tailsCost : Cost)
    (hf : lookupDepth table (.Pair lh lt) (.Pair rh rt) ≤ fuel)
    (hfind : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (hh : Evaluation fuel lh rh table (some heads) afterHeads headsCost)
    (ht : Evaluation fuel lt rt afterHeads (some tails) output tailsCost)
    (ha : U32.checked_add heads.edges tails.edges = none) :
    ∃ lookupCost : LookupSource.Cost,
      Evaluation (fuel + 1) (.Pair lh lt) (.Pair rh rt) table none output
        ((Cost.entry .evaluate).plus (pathCost 238
          (((Slot.ofValue (encodeResult heads)).dropWork.plus (Slot.ofValue (encodeResult tails)).dropWork).plus ⟨5, 0⟩)
          [Legacy.costMap lookupCost, headsCost, tailsCost, Cost.entry .checkedAdd])) ∧
      lookupCost.events = (LookupEvents.lookup table (.Pair lh lt) (.Pair rh rt)).2 := by
  obtain ⟨lc, hl, he⟩ := lookup_none table _ _ fuel hf hfind
  have hp : 0 < fuel := by unfold lookupDepth at hf; omega
  have hadd := checked_add_source fuel hp heads.edges tails.edges
  rw [ha] at hadd
  refine ⟨lc, ⟨source_of_exec fuel _ _ _ (subtotal_overflow_exec _ table lh lt rh rt heads tails afterHeads output _ _ _ _
    hl hh.source ht.source hadd), ?_⟩, he⟩
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  simp only [hh.native, ht.native, bind_ok, uncurry_apply_pair, lift, ha]

theorem root_overflow_step (table : MemoTable) (lh lt rh rt : BalancedWord) (heads tails : CommonEmbedding) (subtotal : U32)
    (afterHeads output : MemoTable) (fuel : Nat) (headsCost tailsCost : Cost)
    (hf : lookupDepth table (.Pair lh lt) (.Pair rh rt) ≤ fuel)
    (hfind : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (hh : Evaluation fuel lh rh table (some heads) afterHeads headsCost)
    (ht : Evaluation fuel lt rt afterHeads (some tails) output tailsCost)
    (ha : U32.checked_add heads.edges tails.edges = some subtotal) (hr : U32.checked_add subtotal 1#u32 = none) :
    ∃ lookupCost : LookupSource.Cost,
      Evaluation (fuel + 1) (.Pair lh lt) (.Pair rh rt) table none output
        ((Cost.entry .evaluate).plus (pathCost 260
          (((Slot.ofValue (encodeResult heads)).dropWork.plus (Slot.ofValue (encodeResult tails)).dropWork).plus ⟨5, 0⟩)
          [Legacy.costMap lookupCost, headsCost, tailsCost, Cost.entry .checkedAdd, Cost.entry .checkedAdd])) ∧
      lookupCost.events = (LookupEvents.lookup table (.Pair lh lt) (.Pair rh rt)).2 := by
  obtain ⟨lc, hl, he⟩ := lookup_none table _ _ fuel hf hfind
  have hp : 0 < fuel := by unfold lookupDepth at hf; omega
  have hadd := checked_add_source fuel hp heads.edges tails.edges
  rw [ha] at hadd
  have hroot := checked_add_source fuel hp subtotal 1#u32
  rw [hr] at hroot
  refine ⟨lc, ⟨source_of_exec fuel _ _ _ (root_overflow_exec _ table lh lt rh rt heads tails subtotal afterHeads output _ _ _ _ _
    hl hh.source ht.source hadd (by simpa using hroot)), ?_⟩, he⟩
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  simp only [hh.native, ht.native, bind_ok, uncurry_apply_pair, lift, ha, hr]


theorem box_source (fuel : Nat) (hf : 0 < fuel) (value : Value) :
    run Certificate.original.body fuel .boxNew [value] = some (.boxed value, Cost.entry .boxNew) := by
  cases fuel with
  | zero => omega
  | succ _ => rfl

theorem left_failure_step (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails : CommonEmbedding) (subtotal total : U32) (afterHeads afterTails output : MemoTable)
    (fuel : Nat) (headsCost tailsCost leftCost : Cost)
    (hf : lookupDepth table (.Pair lh lt) (.Pair rh rt) ≤ fuel) (hc : MemoSource.concatenateDepth lh lt ≤ fuel)
    (hfind : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (hh : Evaluation fuel lh rh table (some heads) afterHeads headsCost)
    (ht : Evaluation fuel lt rt afterHeads (some tails) afterTails tailsCost)
    (ha : U32.checked_add heads.edges tails.edges = some subtotal) (hr : U32.checked_add subtotal 1#u32 = some total)
    (hd : Evaluation fuel (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails none output leftCost) :
    ∃ lookupCost concatCost : LookupSource.Cost,
      Evaluation (fuel + 1) (.Pair lh lt) (.Pair rh rt) table none output
        ((Cost.entry .evaluate).plus (pathCost 373
          (((Slot.ofValue (encodeResult (matched heads tails total))).dropWork.plus
            (Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))).dropWork).plus ⟨11, 0⟩)
          [Legacy.costMap lookupCost, headsCost, tailsCost, Cost.entry .checkedAdd, Cost.entry .checkedAdd,
            Cost.entry .boxNew, Cost.entry .boxNew, Legacy.costMap concatCost, leftCost])) ∧
      lookupCost.events = (LookupEvents.lookup table (.Pair lh lt) (.Pair rh rt)).2 ∧
      concatCost.events = MemoSource.concatenateEvents lh lt := by
  obtain ⟨lc, hl, he⟩ := lookup_none table _ _ fuel hf hfind
  obtain ⟨cc, hconcat, hce⟩ := Helpers.concatenate_source lh lt fuel hc
  have hp : 0 < fuel := by unfold lookupDepth at hf; omega
  have hadd := checked_add_source fuel hp heads.edges tails.edges
  rw [ha] at hadd
  have hroot := checked_add_source fuel hp subtotal 1#u32
  rw [hr] at hroot
  have hbh := box_source fuel hp (encodeWord heads.word)
  have hbt := box_source fuel hp (encodeWord tails.word)
  refine ⟨lc, cc, ⟨source_of_exec fuel _ _ _ (left_failure_exec _ table lh lt rh rt heads tails subtotal total _
    afterHeads afterTails output _ _ _ _ _ _ _ _ _ hl hh.source ht.source hadd (by simpa using hroot) hbh hbt hconcat hd.source), ?_⟩, he, hce⟩
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  simp only [hh.native, ht.native, bind_ok, uncurry_apply_pair, lift, ha, hr, OrderedSolver.concatenate_correct, hd.native]

theorem right_failure_step (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails dropLeft : CommonEmbedding) (subtotal total : U32) (afterHeads afterTails afterLeft output : MemoTable)
    (fuel : Nat) (headsCost tailsCost leftCost rightCost : Cost)
    (hf : lookupDepth table (.Pair lh lt) (.Pair rh rt) ≤ fuel)
    (hc : MemoSource.concatenateDepth lh lt ≤ fuel) (hcr : MemoSource.concatenateDepth rh rt ≤ fuel)
    (hfind : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (hh : Evaluation fuel lh rh table (some heads) afterHeads headsCost)
    (ht : Evaluation fuel lt rt afterHeads (some tails) afterTails tailsCost)
    (ha : U32.checked_add heads.edges tails.edges = some subtotal) (hr : U32.checked_add subtotal 1#u32 = some total)
    (hdl : Evaluation fuel (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails (some dropLeft) afterLeft leftCost)
    (hdr : Evaluation fuel (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft none output rightCost) :
    ∃ lookupCost concatCost concatRightCost : LookupSource.Cost,
      Evaluation (fuel + 1) (.Pair lh lt) (.Pair rh rt) table none output
        ((Cost.entry .evaluate).plus (pathCost 449
          (((((Slot.ofValue (encodeResult (matched heads tails total))).dropWork.plus
            (Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))).dropWork).plus
            (Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))).dropWork).plus
            (Slot.ofValue (encodeResult dropLeft)).dropWork).plus ⟨13, 0⟩)
          [Legacy.costMap lookupCost, headsCost, tailsCost, Cost.entry .checkedAdd, Cost.entry .checkedAdd,
            Cost.entry .boxNew, Cost.entry .boxNew, Legacy.costMap concatCost, leftCost, Legacy.costMap concatRightCost, rightCost])) ∧
      lookupCost.events = (LookupEvents.lookup table (.Pair lh lt) (.Pair rh rt)).2 ∧
      concatCost.events = MemoSource.concatenateEvents lh lt ∧ concatRightCost.events = MemoSource.concatenateEvents rh rt := by
  obtain ⟨lc, hl, he⟩ := lookup_none table _ _ fuel hf hfind
  obtain ⟨cc, hconcat, hce⟩ := Helpers.concatenate_source lh lt fuel hc
  obtain ⟨cr, hconcatRight, hcre⟩ := Helpers.concatenate_source rh rt fuel hcr
  have hp : 0 < fuel := by unfold lookupDepth at hf; omega
  have hadd := checked_add_source fuel hp heads.edges tails.edges
  rw [ha] at hadd
  have hroot := checked_add_source fuel hp subtotal 1#u32
  rw [hr] at hroot
  have hbh := box_source fuel hp (encodeWord heads.word)
  have hbt := box_source fuel hp (encodeWord tails.word)
  refine ⟨lc, cc, cr, ⟨source_of_exec fuel _ _ _ (right_failure_exec _ table lh lt rh rt heads tails dropLeft subtotal total _ _
    afterHeads afterTails afterLeft output _ _ _ _ _ _ _ _ _ _ _ hl hh.source ht.source hadd (by simpa using hroot)
    hbh hbt hconcat hdl.source hconcatRight hdr.source), ?_⟩, he, hce, hcre⟩
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  simp only [hh.native, ht.native, bind_ok, uncurry_apply_pair, lift, ha, hr, OrderedSolver.concatenate_correct, hdl.native, hdr.native]

end SubtreeProofs.Rust.SourceEval.Evaluator
