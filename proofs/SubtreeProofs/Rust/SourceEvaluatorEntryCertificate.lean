module

public import SubtreeProofs.Rust.SourceEvalBodyCertificate
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
import all SubtreeProofs.Rust.SourceEvalBody

/-! Kernel-checked access to the actual parsed evaluator declaration, including
its 113 locals and the existing certified whole body. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.CallingCertificate

def evaluatorOption : Option TypeReader.Definition :=
  originalProgram.definitions.find? (fun decl => decl.source.function == .evaluate)

theorem evaluator_fields : evaluatorOption.map (fun decl => (decl.source.function, decl.source.localCount, decl.source.code)) =
    some (.evaluate, 113, Evaluator.body) := by
  with_unfolding_all rfl

def originalEvaluator : TypeReader.Definition := evaluatorOption.get (by
  have h := congrArg Option.isSome evaluator_fields
  simpa only [Option.isSome_map, Option.isSome_some] using h)

theorem originalEvaluator_spec : originalEvaluator.source.function = .evaluate ∧
    originalEvaluator.source.localCount = 113 ∧ originalEvaluator.source.code = Evaluator.body := by
  have h := evaluator_fields
  rw [(Option.some_get _ : some originalEvaluator = evaluatorOption).symm] at h
  obtain ⟨hf, rest⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hf, (Prod.mk.inj rest).1, (Prod.mk.inj rest).2⟩

theorem evaluator_lookup : originalProgram.definitions.find? (fun decl => decl.source.function == .evaluate) =
    some originalEvaluator := (Option.some_get _).symm

end SubtreeProofs.Rust.SourceEval.CallingCertificate
