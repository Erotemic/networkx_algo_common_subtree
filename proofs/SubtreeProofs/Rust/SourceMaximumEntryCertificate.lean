module

public import SubtreeProofs.Rust.SourceMaximumBody
public import SubtreeProofs.Rust.SourceEvalCallingCertificate

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
import all SubtreeProofs.Rust.SourceEvalCallingCertificate
import all SubtreeProofs.Rust.SourceMaximumBody

/-! Kernel-checked access to the actual parsed maximum declaration, including
its 7 locals and the existing certified whole body. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.CallingCertificate

def maximumOption : Option TypeReader.Definition :=
  originalProgram.definitions.find? (fun decl => decl.source.function == .maximum)

theorem maximum_fields : maximumOption.map (fun decl => (decl.source.function, decl.source.localCount, decl.source.code)) =
    some (.maximum, 7, Maximum.body) := by
  with_unfolding_all rfl

def originalMaximum : TypeReader.Definition := maximumOption.get (by
  have h := congrArg Option.isSome maximum_fields
  simpa only [Option.isSome_map, Option.isSome_some] using h)

theorem originalMaximum_spec : originalMaximum.source.function = .maximum ∧
    originalMaximum.source.localCount = 7 ∧ originalMaximum.source.code = Maximum.body := by
  have h := maximum_fields
  rw [(Option.some_get _ : some originalMaximum = maximumOption).symm] at h
  obtain ⟨hf, rest⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hf, (Prod.mk.inj rest).1, (Prod.mk.inj rest).2⟩

theorem maximum_lookup : originalProgram.definitions.find? (fun decl => decl.source.function == .maximum) =
    some originalMaximum := (Option.some_get _).symm

end SubtreeProofs.Rust.SourceEval.CallingCertificate
