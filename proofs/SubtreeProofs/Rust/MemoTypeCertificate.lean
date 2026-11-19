module

public import SubtreeProofs.Rust.MemoTypeReader
public import SubtreeProofs.Rust.MemoSourceCertificate

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
import all SubtreeProofs.Rust.MemoSourceFrontend
import all SubtreeProofs.Rust.MemoSourceTypes
import all SubtreeProofs.Rust.MemoTypeReader
import all SubtreeProofs.Rust.Generated.MemoSourceInput
import all SubtreeProofs.Rust.Generated.MemoSourceProgram

/-! Kernel-checked actual memo helper layouts, nested annotations, signatures,
return/argument prefixes and static constraints. Region scope is separate. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.MemoSource.TypeReader.Certificate

theorem original_checked : check Input.Program.source 512 Program.body = true := by decide +kernel

theorem original_boundaries (function : Function) (hf : function ≠ .boxNew) :
    ∃ locals, locals.take ((Types.inputs function).length + 1) = Types.output function :: Types.inputs function ∧
      Types.CodeConstraints locals (Types.output function) (Program.body function) :=
  check_boundaries original_checked function hf

theorem original_declarations :
    ∃ program, read Input.Program.source 512 = .ok program ∧
      ∀ layout ∈ program.layouts,
        LookupSource.Heap.Shape layout.kind layout.variant layout.fields (.adt layout.kind) := by
  obtain ⟨program, hr, hs, _⟩ := check_sound original_checked
  exact ⟨program, hr, hs⟩

end SubtreeProofs.Rust.MemoSource.TypeReader.Certificate
