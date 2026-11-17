module

public import SubtreeProofs.Rust.LookupStackCalls
public import SubtreeProofs.Rust.LookupTypeCertificate

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.LookupSourceCertificate
import all SubtreeProofs.Rust.LookupStackCode
import all SubtreeProofs.Rust.LookupStackState
import all SubtreeProofs.Rust.LookupTypeAnnotations
import all SubtreeProofs.Rust.Generated.LookupSourceInput
import all SubtreeProofs.Rust.Generated.LookupSourceExtraCompareInput

/-! Kernel certificates for retained source storage markers and exact local
declaration counts in both actual extractions. Source regions remain erased;
these certificates establish local storage/initialization discipline. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.LookupSource.Stack.Certificate

def original (function : Function) : Code := (lower (LookupSource.Certificate.original.body function)).getD .done
def mutant (function : Function) : Code := (lower (LookupSource.Certificate.mutant.body function)).getD .done

def originalCount : Function → Nat
  | .copyWord => 10
  | .compare => 15
  | .copyResult => 6
  | .lookup => 20
  | .boxNew => 0

def mutantCount (function : Function) : Nat := if function = .lookup then 23 else originalCount function

theorem original_lower (function : Function) :
    lower (LookupSource.Certificate.original.body function) = some (original function) := by
  cases function <;> with_unfolding_all rfl

theorem mutant_lower (function : Function) :
    lower (LookupSource.Certificate.mutant.body function) = some (mutant function) := by
  cases function <;> with_unfolding_all rfl

theorem original_erase : erased original = Program.body := by
  funext function
  exact Option.some.inj ((lower_erases (original_lower function)).symm.trans
    (LookupSource.Certificate.original_lower function))

theorem mutant_erase : erased mutant = ExtraCompare.body := by
  funext function
  exact Option.some.inj ((lower_erases (mutant_lower function)).symm.trans
    (LookupSource.Certificate.mutant_lower function))

theorem original_checked : BodyChecked original originalCount := by
  intro function hf
  cases function <;> first | contradiction | decide +kernel

theorem mutant_checked : BodyChecked mutant mutantCount := by
  intro function hf
  cases function <;> first | contradiction | decide +kernel

def countsCheck (source : Lean.Json) (fuel : Nat) (counts : Function → Nat) : Bool :=
  match TypeReader.read source fuel with
  | .error _ => false
  | .ok program => program.definitions.all fun decl => decl.locals.length == counts decl.function

theorem countsCheck_sound {source : Lean.Json} {fuel : Nat} {counts : Function → Nat}
    (h : countsCheck source fuel counts = true) :
    ∃ program, TypeReader.read source fuel = .ok program ∧
      ∀ function, function ≠ .boxNew → ∃ decl ∈ program.definitions,
        decl.function = function ∧ decl.locals.length = counts function := by
  cases hr : TypeReader.read source fuel with
  | error message => simp [countsCheck, hr] at h
  | ok program =>
    refine ⟨program, rfl, ?_⟩
    intro function hf
    have hm : function ∈ program.definitions.map TypeReader.Definition.function := by
      rw [program.covers]
      cases function <;> simp_all
    obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
    have hc := List.all_eq_true.mp (by simpa only [countsCheck, hr] using h) decl hd
    have hl : decl.locals.length = counts decl.function := by simpa using hc
    exact ⟨decl, hd, he, by simpa only [he] using hl⟩

theorem original_counts : countsCheck Input.Program.source 512 originalCount = true := by decide +kernel
theorem mutant_counts : countsCheck Input.ExtraCompare.source 512 mutantCount = true := by decide +kernel

theorem original_run_safe (fuel : Nat) (function : Function) (cells : List Heap.Cell) (memory : Heap.Memory)
    {cell : Heap.Cell} {after : Heap.Memory} {cost : Cost} (hargs : cells.length = Frontend.arity function)
    (hr : Heap.run Program.body fuel function cells memory = some (cell, after, cost)) :
    RunSafe original originalCount fuel function cells memory cell after cost :=
  run_sound original originalCount original_checked fuel function cells memory cell after cost hargs
    (by simpa only [original_erase] using hr)

theorem mutant_run_safe (fuel : Nat) (function : Function) (cells : List Heap.Cell) (memory : Heap.Memory)
    {cell : Heap.Cell} {after : Heap.Memory} {cost : Cost} (hargs : cells.length = Frontend.arity function)
    (hr : Heap.run ExtraCompare.body fuel function cells memory = some (cell, after, cost)) :
    RunSafe mutant mutantCount fuel function cells memory cell after cost :=
  run_sound mutant mutantCount mutant_checked fuel function cells memory cell after cost hargs
    (by simpa only [mutant_erase] using hr)

end SubtreeProofs.Rust.LookupSource.Stack.Certificate
