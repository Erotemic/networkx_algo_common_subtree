module

public import SubtreeProofs.Rust.LookupRegionProgram
public import SubtreeProofs.Rust.LookupSourceCertificate

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
import all SubtreeProofs.Rust.LookupBorrowLoans
import all SubtreeProofs.Rust.LookupRegionTypes
import all SubtreeProofs.Rust.LookupRegionReader
import all SubtreeProofs.Rust.LookupRegionScope
import all SubtreeProofs.Rust.LookupRegionProgram
import all SubtreeProofs.Rust.Generated.LookupSourceInput
import all SubtreeProofs.Rust.Generated.LookupSourceExtraCompareInput

/-! Kernel certificates for signature binders, body-region uses, region call
arities and region-bearing local annotations in both retained source programs. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions.Certificate

theorem original_checked : Reader.check Input.Program.source Program.body = true := by decide +kernel
theorem mutant_checked : Reader.check Input.ExtraCompare.source ExtraCompare.body = true := by decide +kernel

end SubtreeProofs.Rust.LookupSource.Heap.Regions.Certificate
