module

public import SubtreeProofs.Rust.SourceEvalRegionProgram
public import SubtreeProofs.Rust.SourceEvalCertificate

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSourceTypes
import all SubtreeProofs.Rust.LookupTypedCode
import all SubtreeProofs.Rust.LookupTypeReader
import all SubtreeProofs.Rust.LookupTypeAnnotations
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupRegionTypes
import all SubtreeProofs.Rust.LookupRegionReader
import all SubtreeProofs.Rust.LookupRegionScope
import all SubtreeProofs.Rust.MemoSourceFrontend
import all SubtreeProofs.Rust.SourceEvalTypes
import all SubtreeProofs.Rust.SourceEvalTypedCode
import all SubtreeProofs.Rust.SourceEvalFrontend
import all SubtreeProofs.Rust.SourceEvalProgram
import all SubtreeProofs.Rust.SourceEvalCertificate
import all SubtreeProofs.Rust.SourceEvalTypeAnnotations
import all SubtreeProofs.Rust.SourceEvalTypeReader
import all SubtreeProofs.Rust.SourceEvalRegionProgram
import all SubtreeProofs.Rust.Generated.SourceEvalInput

/-! Actual nine-definition source/static types and free/body binder scope are
kernel checked, including scalar options and constructed-local borrows. This
checks binding/erasure; dynamic validity of those local loans is separate. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

namespace SubtreeProofs.Rust.SourceEval.Regions.Certificate

open LookupSource.Heap.Regions.Reader

theorem original_checked : check Input.Program.source SourceEval.Certificate.original.body = true := by
  decide +kernel

theorem original_program : ∃ program, read Input.Program.source = .ok program ∧
    ∀ function ∈ ProgramReader.helpers, ∃ decl ∈ program.definitions,
      decl.function = function ∧ decl.source.source.code = SourceEval.Certificate.original.body function ∧
      decl.freeCount = regionArity function := check_sound original_checked

theorem original_mentions_bound : ∃ program, read Input.Program.source = .ok program ∧
    ∀ function ∈ ProgramReader.helpers, ∃ decl ∈ program.definitions,
      decl.function = function ∧ decl.source.source.code = SourceEval.Certificate.original.body function ∧
      (∀ raw, MentionWith (calleeRegions program.info) decl.signatureJson raw →
        ∃ value, region (.signature decl.freeCount) raw = .ok value) ∧
      (∀ raw, MentionWith (calleeRegions program.info) decl.bodyJson raw →
        ∃ value, region (.body decl.bodyCount) raw = .ok value) := by
  obtain ⟨program, hr, hp⟩ := original_program
  refine ⟨program, hr, ?_⟩
  intro function hf
  obtain ⟨decl, hd, he, hc, _⟩ := hp function hf
  exact ⟨decl, hd, he, hc, fun _ hm => decl.signatureScope.mentions_bound hm,
    fun _ hm => decl.bodyScope.mentions_bound hm⟩

end SubtreeProofs.Rust.SourceEval.Regions.Certificate
