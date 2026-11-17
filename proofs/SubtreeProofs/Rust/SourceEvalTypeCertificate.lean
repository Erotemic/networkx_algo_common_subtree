module

public import SubtreeProofs.Rust.SourceEvalTypeReader
public import SubtreeProofs.Rust.SourceEvalCertificate

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.LookupSourceTypes
import all SubtreeProofs.Rust.LookupTypedCode
import all SubtreeProofs.Rust.LookupTypeReader
import all SubtreeProofs.Rust.LookupTypeAnnotations
import all SubtreeProofs.Rust.MemoSourceFrontend
import all SubtreeProofs.Rust.SourceEvalScalar
import all SubtreeProofs.Rust.SourceEvalOperands
import all SubtreeProofs.Rust.SourceEvalMachine
import all SubtreeProofs.Rust.SourceEvalFrontend
import all SubtreeProofs.Rust.SourceEvalProgram
import all SubtreeProofs.Rust.SourceEvalCertificate
import all SubtreeProofs.Rust.SourceEvalTypes
import all SubtreeProofs.Rust.SourceEvalTypedCode
import all SubtreeProofs.Rust.SourceEvalTypeAnnotations
import all SubtreeProofs.Rust.SourceEvalTypeReader
import all SubtreeProofs.Rust.Generated.SourceEvalInput

/-! Kernel-checked actual signatures, local/field/operand/aggregate/call
annotations and every normal control arm for all nine source definitions.
These are static constraints; addressed type preservation and loans are
separate obligations. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

namespace SubtreeProofs.Rust.SourceEval.TypeReader.Certificate

theorem original_checked : check Input.Program.source 512 SourceEval.Certificate.original.body = true := by
  decide +kernel

theorem original_boundaries (function : SourceEval.Function) (hf : function ∈ ProgramReader.helpers) :
    ∃ locals, locals.take ((Types.inputs function).length + 1) = Types.output function :: Types.inputs function ∧
      Types.CodeConstraints locals (Types.output function) (SourceEval.Certificate.original.body function) :=
  check_boundaries original_checked function hf

theorem original_declarations :
    ∃ program, read Input.Program.source 512 = .ok program ∧
      (∀ layout ∈ program.layouts,
        LookupSource.Heap.Shape layout.kind layout.variant layout.fields (.adt layout.kind)) ∧
      (∀ layout ∈ program.scoreLayouts,
        LookupSource.Heap.Shape layout.kind layout.variant layout.fields (.option .u32)) ∧
      program.definitions.map Definition.source = program.source.definitions := by
  obtain ⟨program, hr, hs, hu, _⟩ := check_sound original_checked
  exact ⟨program, hr, hs, hu, program.aligned⟩

end SubtreeProofs.Rust.SourceEval.TypeReader.Certificate
