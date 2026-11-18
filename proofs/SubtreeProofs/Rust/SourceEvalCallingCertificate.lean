module

public import SubtreeProofs.Rust.SourceEvalCallingChoice
public import SubtreeProofs.Rust.SourceEvalTypeCertificate

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


/-! Executable access to the already checked actual typed source declarations.
The concrete choice declaration retains its parsed function, local count and
body; calling consumers do not construct a substitute declaration. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

namespace SubtreeProofs.Rust.SourceEval.CallingCertificate

def originalProgram : TypeReader.Program :=
  (TypeReader.read Input.Program.source 512).toOption.get (by
    obtain ⟨program, hr, _⟩ := TypeReader.Certificate.original_declarations
    rw [hr]
    rfl)

theorem originalProgram_read : TypeReader.read Input.Program.source 512 = .ok originalProgram := by
  have get_read {α : Type} (result : Except String α) (ready : result.toOption.isSome = true) :
      result = .ok (result.toOption.get ready) := by
    cases result with
    | error _ => cases ready
    | ok _ => rfl
  exact get_read _ _

def choiceOption : Option TypeReader.Definition :=
  originalProgram.definitions.find? (fun decl => decl.source.function == .chooseLonger)

theorem choice_fields : choiceOption.map (fun decl => (decl.source.function, decl.source.localCount, decl.source.code)) =
    some (.chooseLonger, 6, Choice.body) := by
  with_unfolding_all rfl

def originalChoice : TypeReader.Definition := choiceOption.get (by
  have h := congrArg Option.isSome choice_fields
  simpa only [Option.isSome_map, Option.isSome_some] using h)

theorem originalChoice_spec : originalChoice.source.function = .chooseLonger ∧
    originalChoice.source.localCount = 6 ∧ originalChoice.source.code = Choice.body := by
  have h := choice_fields
  have ho : choiceOption = some originalChoice := (Option.some_get _).symm
  rw [ho] at h
  obtain ⟨hf, rest⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hf, (Prod.mk.inj rest).1, (Prod.mk.inj rest).2⟩

end SubtreeProofs.Rust.SourceEval.CallingCertificate
