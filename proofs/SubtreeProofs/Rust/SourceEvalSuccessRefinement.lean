module

public import SubtreeProofs.Rust.SourceEvalSuccess
public import SubtreeProofs.Rust.SourceEvalFailureRefinement
public import SubtreeProofs.Rust.SourceEvalChoiceRefinement

/-! Actual source/native successful recursive composition, consuming the seven
completed helper contracts. Smaller recursive evaluations remain explicit and
are discharged by the whole-run induction. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource LookupSource.Partial verified_ordered_core Aeneas Aeneas.Std Result

private theorem choose_source (fuel : Nat) (hf : 0 < fuel) (first last : CommonEmbedding) :
    run Certificate.original.body fuel .chooseLonger [encodeResult first, encodeResult last] =
      some (encodeResult (OrderedSolver.selectResult first last), Choice.cost first last) := by
  cases fuel with
  | zero => omega
  | succ fuel => exact Choice.source_run fuel first last

theorem success_step (table : MemoTable) (lh lt rh rt : BalancedWord)
    (heads tails dropLeft dropRight : CommonEmbedding) (subtotal total : U32)
    (afterHeads afterTails afterLeft afterRight : MemoTable) (fuel : Nat) (headsCost tailsCost leftCost rightCost : Cost)
    (hf : lookupDepth table (.Pair lh lt) (.Pair rh rt) ≤ fuel)
    (hc : MemoSource.concatenateDepth lh lt ≤ fuel) (hcr : MemoSource.concatenateDepth rh rt ≤ fuel)
    (hfind : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (hh : Evaluation fuel lh rh table (some heads) afterHeads headsCost)
    (ht : Evaluation fuel lt rt afterHeads (some tails) afterTails tailsCost)
    (ha : U32.checked_add heads.edges tails.edges = some subtotal) (hr : U32.checked_add subtotal 1#u32 = some total)
    (hdl : Evaluation fuel (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails (some dropLeft) afterLeft leftCost)
    (hdr : Evaluation fuel (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft (some dropRight) afterRight rightCost)
    (hi : MemoSource.insertDepth (.Pair lh lt) (.Pair rh rt)
      (OrderedSolver.selectResult (OrderedSolver.selectResult (matched heads tails total) dropLeft) dropRight) ≤ fuel) :
    let first := OrderedSolver.selectResult (matched heads tails total) dropLeft
    let result := OrderedSolver.selectResult first dropRight
    ∃ lookupCost concatCost concatRightCost insertCost : LookupSource.Cost,
      Evaluation (fuel + 1) (.Pair lh lt) (.Pair rh rt) table (some result)
        (.Entry ⟨.Pair lh lt, .Pair rh rt, result⟩ afterRight)
        ((Cost.entry .evaluate).plus (pathCost 525
          (((Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))).dropWork.plus
            (Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))).dropWork).plus ⟨13, 0⟩)
          [Legacy.costMap lookupCost, headsCost, tailsCost, Cost.entry .checkedAdd, Cost.entry .checkedAdd,
            Cost.entry .boxNew, Cost.entry .boxNew, Legacy.costMap concatCost, leftCost, Legacy.costMap concatRightCost, rightCost,
            Choice.cost (matched heads tails total) dropLeft, Choice.cost first dropRight, Legacy.costMap insertCost])) ∧
      lookupCost.events = (LookupEvents.lookup table (.Pair lh lt) (.Pair rh rt)).2 ∧
      concatCost.events = MemoSource.concatenateEvents lh lt ∧ concatRightCost.events = MemoSource.concatenateEvents rh rt ∧
      insertCost.events = MemoSource.insertEvents (.Pair lh lt) (.Pair rh rt) result := by
  dsimp only
  obtain ⟨lc, hl, he⟩ := lookup_none table _ _ fuel hf hfind
  obtain ⟨cc, hconcat, hce⟩ := Helpers.concatenate_source lh lt fuel hc
  obtain ⟨cr, hconcatRight, hcre⟩ := Helpers.concatenate_source rh rt fuel hcr
  obtain ⟨ci, hins, hie⟩ := Helpers.insert_source afterRight (.Pair lh lt) (.Pair rh rt) _ fuel hi
  have hp : 0 < fuel := by unfold lookupDepth at hf; omega
  have hadd := checked_add_source fuel hp heads.edges tails.edges
  rw [ha] at hadd
  have hroot := checked_add_source fuel hp subtotal 1#u32
  rw [hr] at hroot
  have hbh := box_source fuel hp (encodeWord heads.word)
  have hbt := box_source fuel hp (encodeWord tails.word)
  have hchoice := choose_source fuel hp (matched heads tails total) dropLeft
  have hfinal := choose_source fuel hp (OrderedSolver.selectResult (matched heads tails total) dropLeft) dropRight
  refine ⟨lc, cc, cr, ci, ⟨source_of_exec fuel _ _ _ (success_exec _ table lh lt rh rt heads tails dropLeft dropRight _ _ subtotal total _ _
    afterHeads afterTails afterLeft afterRight _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl hh.source ht.source hadd (by simpa using hroot)
    hbh hbt hconcat hdl.source hconcatRight hdr.source hchoice hfinal hins), ?_⟩, he, hce, hcre, hie⟩
  rw [memoized_common_embedding.eq_def, MemoizedOrderedSolver.memo_lookup_correct, hfind, bind_ok]
  simp only [hh.native, ht.native, bind_ok, uncurry_apply_pair, lift, ha, hr, OrderedSolver.concatenate_correct,
    hdl.native, hdr.native, OrderedSolver.choose_longer_correct, MemoizedOrderedSolver.memo_insert_correct, matched]

end SubtreeProofs.Rust.SourceEval.Evaluator
