module

public import SubtreeProofs.Rust.SourcePairNativeFreshClosure
public import SubtreeProofs.Rust.SourceContractionRequests

/-! Universal addressed evaluator existence with complete ownership, protected
caller reads, witness provenance and exact stability at larger sufficient bounds.
Induction uses independent query semilength, including both contractions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open verified_ordered_core

theorem native_total_fresh (left right : BalancedWord) : NativeTotalFresh left right := by
  cases left with
  | Empty => exact native_empty_total_fresh .Empty right (Or.inl rfl)
  | Pair lh lt =>
    cases right with
    | Empty => exact native_empty_total_fresh (.Pair lh lt) .Empty (Or.inr rfl)
    | Pair rh rt =>
      exact pair_native_total_fresh lh lt rh rt
        (native_total_fresh lh rh) (native_total_fresh lt rt)
        (native_total_fresh (OrderedSolver.appendWord lh lt) (.Pair rh rt))
        (native_total_fresh (.Pair lh lt) (OrderedSolver.appendWord rh rt))
termination_by (OrderedSolver.toDyck left).semilength + (OrderedSolver.toDyck right).semilength
decreasing_by
  all_goals simp only [OrderedSolver.toDyck_appendWord, OrderedSolver.toDyck, DyckWord.semilength_add, DyckWord.semilength_nest]
  all_goals omega

theorem native_total (left right : BalancedWord) : NativeTotal left right :=
  NativeTotalFresh.total (native_total_fresh left right)

end SubtreeProofs.Rust.SourceEval.Evaluator
