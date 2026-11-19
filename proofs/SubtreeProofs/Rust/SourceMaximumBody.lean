module

public import SubtreeProofs.Rust.SourceEvalBodyCertificate

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
import all SubtreeProofs.Rust.SourceEvalCertificate

/-! Reviewable public maximum control with kernel identity to the actual parsed
source. The table drop stays explicit after moving the returned option. Body
identity alone supplies neither successful execution nor cleanup safety. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource

def beforeCall : List Action := [
  .storageLive 0, .storageLive 3, .storageLive 4,
  .assign 4 (.address (.deref (.local 1))),
  .storageLive 5, .assign 5 (.address (.deref (.local 2))),
  .storageLive 6, .assign 6 (.aggregate .table 0 [])]

def evaluateCall : Action :=
  .call .evaluate [.move (.local 4), .move (.local 5), .move (.local 6)] 3

def afterCall : List Action := [
  .storageDead 6, .storageDead 5, .storageDead 4,
  .assign 0 (.use (.move (.field (.local 3) none 0))),
  .drop 3, .storageDead 3, .storageDead 2, .storageDead 1]

def body : Code := (beforeCall ++ [evaluateCall] ++ afterCall).foldr Control.Tree.step .ret

set_option maxRecDepth 32768 in
set_option maxHeartbeats 200000000 in
theorem actual_body : Certificate.original.body .maximum = body := by
  with_unfolding_all rfl

end SubtreeProofs.Rust.SourceEval.Maximum
