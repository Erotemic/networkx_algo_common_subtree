module

public import SubtreeProofs.Rust.SourceEvalLegacyRun
public import SubtreeProofs.Rust.SourceEvalCertificate
public import SubtreeProofs.Rust.LookupSourceCertificate
public import SubtreeProofs.Rust.MemoSourceCertificate

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSource
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.LookupSourceTypes
import all SubtreeProofs.Rust.LookupTypeReader
import all SubtreeProofs.Rust.LookupTypeAnnotations
import all SubtreeProofs.Rust.LookupSourceCertificate
import all SubtreeProofs.Rust.Generated.LookupSourceInput
import all SubtreeProofs.Rust.MemoSource
import all SubtreeProofs.Rust.MemoSourceFrontend
import all SubtreeProofs.Rust.MemoSourceCertificate
import all SubtreeProofs.Rust.Generated.MemoSourceInput
import all SubtreeProofs.Rust.SourceEvalLegacyValues
import all SubtreeProofs.Rust.SourceEvalLegacyActions
import all SubtreeProofs.Rust.SourceEvalLegacyControl
import all SubtreeProofs.Rust.SourceEvalMachine
import all SubtreeProofs.Rust.SourceEvalScalar
import all SubtreeProofs.Rust.SourceEvalFrontend
import all SubtreeProofs.Rust.SourceEvalProgram
import all SubtreeProofs.Rust.SourceEvalCertificate
import all SubtreeProofs.Rust.Generated.SourceEvalInput

/-! Kernel-checked identity of the actual evaluator extraction's six helper
bodies with the previously certified helper bodies, under the proved profile
embedding. No generated control template or native proof oracle is used. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000000

namespace SubtreeProofs.Rust.SourceEval.Helpers

open LookupSource Legacy

def lookupFunction : LookupSource.Function → SourceEval.Function
  | .copyWord => .copyWord
  | .compare => .compare
  | .copyResult => .copyResult
  | .lookup => .lookup
  | .boxNew => .boxNew

def memoFunction : MemoSource.Function → SourceEval.Function
  | .copyWord => .copyWord
  | .copyResult => .copyResult
  | .concatenate => .concatenate
  | .insert => .insert
  | .boxNew => .boxNew

theorem lookup_body (function : LookupSource.Function) :
    Certificate.original.body (lookupFunction function) =
      codeMap lookupFunction (LookupSource.Certificate.original.body function) := by
  cases function <;> with_unfolding_all rfl

theorem memo_body (function : MemoSource.Function) :
    Certificate.original.body (memoFunction function) =
      codeMap memoFunction (MemoSource.Certificate.original.body function) := by
  cases function <;> with_unfolding_all rfl

end SubtreeProofs.Rust.SourceEval.Helpers
