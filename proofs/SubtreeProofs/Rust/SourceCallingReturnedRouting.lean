module

public import SubtreeProofs.Rust.SourceEvalCallingControl

/-! Returning selected branches bypass joins in the actual calling executor. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem exec_switch_right_returned {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation} {scrut : Scrutinee} {key : Key}
    {cases : List (Key × Nat)} {fallback : Option Nat} {zero one rest : Code} {packet : ValueCell} {cost : Cost}
    (inspect : Derived.scrutinee world active callers scrut = some (key, active))
    (selected : Control.selectIndex key cases fallback = some 1)
    (branch : exec callee callers one world active = some (.returned final after packet, cost)) :
    exec callee callers (.switch scrut cases fallback zero one rest) world active =
      some (.returned final after packet, (Cost.local (1 + scrut.weight)).plus cost) := by
  rw [exec_switch, inspect]
  simp only [Control.selectSource, selected, bind, Option.bind, branch]

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
