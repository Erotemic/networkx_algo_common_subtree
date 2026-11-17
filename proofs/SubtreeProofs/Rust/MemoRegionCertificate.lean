module

public import SubtreeProofs.Rust.MemoRegionProgram

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
import all SubtreeProofs.Rust.MemoSourceTypes
import all SubtreeProofs.Rust.MemoTypeReader
import all SubtreeProofs.Rust.MemoRegionProgram
import all SubtreeProofs.Rust.Generated.MemoSourceInput
import all SubtreeProofs.Rust.Generated.MemoSourceProgram

/-! The actual memo extraction passes source/static typing and free/body region
scope checking in the kernel. Dynamic lifetime/loan interpretation is separate. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.MemoSource.Regions.Certificate

theorem original_checked : check Input.Program.source Program.body = true := by decide +kernel

theorem original_program : ∃ program, read Input.Program.source = .ok program ∧
    ∀ function, function ≠ .boxNew → ∃ decl ∈ program.definitions,
      decl.function = function ∧ decl.source.code = Program.body function :=
  check_sound original_checked

end SubtreeProofs.Rust.MemoSource.Regions.Certificate
