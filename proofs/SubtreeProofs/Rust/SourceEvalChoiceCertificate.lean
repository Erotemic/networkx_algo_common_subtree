module

public import SubtreeProofs.Rust.SourceEvalChoiceProgram
public import SubtreeProofs.Rust.SourceEvalCertificate

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.LookupSourceTypes
import all SubtreeProofs.Rust.LookupTypeReader
import all SubtreeProofs.Rust.LookupTypeAnnotations
import all SubtreeProofs.Rust.MemoSourceFrontend
import all SubtreeProofs.Rust.SourceEvalScalar
import all SubtreeProofs.Rust.SourceEvalMachine
import all SubtreeProofs.Rust.SourceEvalFrontend
import all SubtreeProofs.Rust.SourceEvalProgram
import all SubtreeProofs.Rust.Generated.SourceEvalInput

import all SubtreeProofs.Rust.SourceEvalChoiceProgram
import all SubtreeProofs.Rust.SourceEvalCertificate

/-! Actual retained-source identity for score choice, checked in the kernel. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

namespace SubtreeProofs.Rust.SourceEval.Choice

theorem actual_body : Certificate.original.body .chooseLonger = body := by
  with_unfolding_all rfl

end SubtreeProofs.Rust.SourceEval.Choice
