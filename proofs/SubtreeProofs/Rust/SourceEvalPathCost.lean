module

public import SubtreeProofs.Rust.SourceEvalMachine

/-! Exact path-cost packaging: literal local source work/destruction plus the
complete costs returned by executed callees. There is no assumed run-level cap. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval

open LookupSource.Partial

def pathCost (steps : Nat) (destroyed : DropWork) (calls : List Cost) : Cost :=
  (Cost.local steps destroyed).plus (calls.foldr Cost.plus {})

end SubtreeProofs.Rust.SourceEval
