module

public import SubtreeProofs.Rust.LookupTypeAnnotations
public import SubtreeProofs.Rust.LookupSourceCertificate

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSourceTypes
import all SubtreeProofs.Rust.LookupTypedCode
import all SubtreeProofs.Rust.LookupTypeReader
import all SubtreeProofs.Rust.LookupTypeAnnotations
import all SubtreeProofs.Rust.Generated.LookupSourceInput
import all SubtreeProofs.Rust.Generated.LookupSourceExtraCompareInput

/-! Kernel certificates for lifetime-erased declarations, annotations and
static constraints in both actual retained source extractions. This does not
claim operational type preservation, borrow/lifetime or Rust adequacy. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.LookupSource.TypeReader.Certificate

theorem original_checked : check Input.Program.source 512 Program.body = true := by decide +kernel

theorem mutant_checked : check Input.ExtraCompare.source 512 ExtraCompare.body = true := by decide +kernel

theorem original_functions (function : Function) (hf : function ≠ .boxNew) :
    ∃ locals, SourceTypes.CodeConstraints locals (SourceTypes.output function) (Program.body function) :=
  check_functions original_checked function hf

theorem mutant_functions (function : Function) (hf : function ≠ .boxNew) :
    ∃ locals, SourceTypes.CodeConstraints locals (SourceTypes.output function) (ExtraCompare.body function) :=
  check_functions mutant_checked function hf

theorem original_declarations :
    ∃ program, read Input.Program.source 512 = .ok program ∧
      ∀ layout ∈ program.layouts,
        Heap.Shape layout.kind layout.variant layout.fields (.adt layout.kind) := by
  obtain ⟨program, hr, hs, _⟩ := check_sound original_checked
  exact ⟨program, hr, hs⟩

end SubtreeProofs.Rust.LookupSource.TypeReader.Certificate
