module

public import SubtreeProofs.Rust.SourceEvalProgram
public import SubtreeProofs.Rust.Generated.SourceEvalInput

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

/-! Kernel-checked reading of the actual evaluator/public-core source into
retained source control and partial-local primitives. This is source-profile
coverage, not yet functional refinement or typed addressed memory adequacy. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

namespace SubtreeProofs.Rust.SourceEval.Certificate

open ProgramReader

def fallback : Program :=
  ⟨helpers.map (fun function => ⟨function, 0, .done⟩), by simp [List.map_map, Function.comp_def]⟩

def original : Program := (read Input.Program.source 512).toOption.getD fallback

theorem original_read : read Input.Program.source 512 = .ok original := by
  with_unfolding_all rfl

theorem original_covers : original.definitions.map Definition.function = helpers := original.covers

theorem original_counts : original.definitions.map (fun decl => (decl.function, decl.localCount)) =
    [(.copyWord, 10), (.compare, 15), (.copyResult, 6), (.lookup, 20),
     (.concatenate, 13), (.insert, 15), (.chooseLonger, 6), (.evaluate, 113), (.maximum, 7)] := by
  with_unfolding_all rfl

def executeSource (json : Lean.Json) (budget fuel : Nat) (function : Function) (args : List LookupSource.Value) :
    LookupSource.Frontend.Read (Option (LookupSource.Value × Cost)) := do
  let program ← read json budget
  pure (run program.body fuel function args)

theorem original_execute (fuel : Nat) (function : Function) (args : List LookupSource.Value) :
    executeSource Input.Program.source 512 fuel function args = .ok (run original.body fuel function args) := by
  simp only [executeSource, original_read, bind, Except.bind, pure, Except.pure]

end SubtreeProofs.Rust.SourceEval.Certificate
