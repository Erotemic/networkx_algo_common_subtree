module

public import SubtreeProofs.Rust.MemoSourceFrontend
public import SubtreeProofs.Rust.Generated.MemoSourceProgram
public import SubtreeProofs.Rust.Generated.MemoSourceInput

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.MemoSourceFrontend
import all SubtreeProofs.Rust.MemoSource
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupSource
import all SubtreeProofs.Rust.Generated.MemoSourceInput
import all SubtreeProofs.Rust.Generated.MemoSourceProgram

/-! Kernel-checked actual insertion and concatenation source normalization.
These certificates retain normal-path control, source moves and complete
instruction/event costs in the existing snapshot primitive interpretation.
Heap/loan/owner refinement is a subsequent, separately named obligation. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.MemoSource.Certificate

open LookupSource

def original : Frontend.Program :=
  (Frontend.read Input.Program.source 512).toOption.getD ⟨.done, .done, .done, .done⟩

theorem original_read : Frontend.read Input.Program.source 512 = .ok original := by
  with_unfolding_all rfl

theorem original_lower (function : Function) :
    Control.lower (original.body function) = some (Program.body function) := by
  cases function <;> with_unfolding_all rfl

theorem original_exec (call : Calls) (function : Function) (env : Env) :
    Control.exec call (original.body function) env = LookupSource.exec call (Program.body function) env :=
  Control.exec_lower call _ _ (original_lower function) env

theorem original_run : sourceRun original.body = run Program.body :=
  run_lower original.body Program.body original_lower

end SubtreeProofs.Rust.MemoSource.Certificate
