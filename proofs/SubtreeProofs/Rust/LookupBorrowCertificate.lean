module

public import SubtreeProofs.Rust.LookupBorrowLoans
public import SubtreeProofs.Rust.LookupTypeCertificate

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
import all SubtreeProofs.Rust.Generated.LookupSourceInput
import all SubtreeProofs.Rust.Generated.LookupSourceExtraCompareInput

/-! Checked source routes for every shared borrow. Concrete parsing, local
types, body correspondence and routes are validated in the kernel. The source
reader still erases region identities; this certificate does not check them. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

def BodiesChecked (body : Function → LookupSource.Code) : Prop :=
  ∀ function, function ≠ .boxNew → ∃ locals,
    locals.take ((SourceTypes.inputs function).length + 1) = SourceTypes.output function :: SourceTypes.inputs function ∧
    SourceTypes.CodeConstraints locals (SourceTypes.output function) (body function) ∧
    codeRoutes locals (body function) = true

def check (source : Lean.Json) (fuel : Nat) (body : Function → LookupSource.Code) : Bool :=
  match TypeReader.read source fuel with
  | .error _ => false
  | .ok program => program.definitions.all fun decl =>
    decide (decl.code = body decl.function) && codeRoutes decl.locals decl.code

theorem check_sound {source : Lean.Json} {fuel : Nat} {body : Function → LookupSource.Code}
    (h : check source fuel body = true) : BodiesChecked body := by
  cases hr : TypeReader.read source fuel with
  | error message => simp [check, hr] at h
  | ok program =>
    intro function hf
    have hm : function ∈ program.definitions.map TypeReader.Definition.function := by
      rw [program.covers]
      cases function <;> simp_all
    obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
    have hc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (by simpa only [check, hr] using h) decl hd)
    have hcode : decl.code = body decl.function := of_decide_eq_true hc.1
    have hconstraints := decl.constraints
    have hboundary := decl.boundary
    have hroutes := hc.2
    rw [hcode, he] at hconstraints hroutes
    rw [he] at hboundary
    exact ⟨decl.locals, hboundary, hconstraints, hroutes⟩

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

theorem original_checked : check Input.Program.source 512 Program.body = true := by decide +kernel
theorem mutant_checked : check Input.ExtraCompare.source 512 ExtraCompare.body = true := by decide +kernel

theorem original_bodies : BodiesChecked Program.body := check_sound original_checked
theorem mutant_bodies : BodiesChecked ExtraCompare.body := check_sound mutant_checked

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
