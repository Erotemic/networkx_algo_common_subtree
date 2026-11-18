module

public import SubtreeProofs.Rust.SourcePairHeadPrefix

/-! Both native concatenated contraction requests strictly decrease the same
independent Dyck-word measure as head and tail recursion. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open verified_ordered_core

theorem left_contraction_request_smaller (lh lt rh rt : BalancedWord) :
    (OrderedSolver.toDyck (OrderedSolver.appendWord lh lt)).semilength +
        (OrderedSolver.toDyck (.Pair rh rt)).semilength <
      (OrderedSolver.toDyck (.Pair lh lt)).semilength +
        (OrderedSolver.toDyck (.Pair rh rt)).semilength := by
  simp only [OrderedSolver.toDyck_appendWord, OrderedSolver.toDyck,
    DyckWord.semilength_add, DyckWord.semilength_nest]
  omega

theorem right_contraction_request_smaller (lh lt rh rt : BalancedWord) :
    (OrderedSolver.toDyck (.Pair lh lt)).semilength +
        (OrderedSolver.toDyck (OrderedSolver.appendWord rh rt)).semilength <
      (OrderedSolver.toDyck (.Pair lh lt)).semilength +
        (OrderedSolver.toDyck (.Pair rh rt)).semilength := by
  simp only [OrderedSolver.toDyck_appendWord, OrderedSolver.toDyck,
    DyckWord.semilength_add, DyckWord.semilength_nest]
  omega

end SubtreeProofs.Rust.SourceEval.Evaluator
