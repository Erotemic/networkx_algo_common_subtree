module

public import SubtreeProofs.Rust.MemoStackCalls
public import SubtreeProofs.Rust.MemoTypeCertificate

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.MemoSourceCertificate
import all SubtreeProofs.Rust.MemoSourceFrontend
import all SubtreeProofs.Rust.LookupStackCode
import all SubtreeProofs.Rust.LookupStackState
import all SubtreeProofs.Rust.MemoTypeReader
import all SubtreeProofs.Rust.Generated.MemoSourceInput


/-! Kernel certificates for retained source storage markers and exact local
declaration counts in the actual memo extraction. These certificates establish
local storage/initialization discipline. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.MemoSource.Stack.Certificate

open LookupSource LookupSource.Stack

def original (function : Function) : Code := (lower (MemoSource.Certificate.original.body function)).getD .done
def originalCount : Function → Nat
  | .copyWord => 10
  | .copyResult => 6
  | .concatenate => 13
  | .insert => 15
  | .boxNew => 0

theorem original_lower (function : Function) :
    lower (MemoSource.Certificate.original.body function) = some (original function) := by
  cases function <;> with_unfolding_all rfl

theorem original_erase : erased original = Program.body := by
  funext function
  exact Option.some.inj ((lower_erases (original_lower function)).symm.trans
    (MemoSource.Certificate.original_lower function))

theorem original_checked : BodyChecked original originalCount := by
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

theorem original_initial_length (function : Function) (hf : function ≠ .boxNew) :
    (initial (originalCount function) (arity function)).length = originalCount function := by
  cases function <;> first | contradiction | decide +kernel

theorem original_run_safe (fuel : Nat) (function : Function) (cells : List Heap.Cell) (memory : Heap.Memory)
    {cell : Heap.Cell} {after : Heap.Memory} {cost : Cost} (hargs : cells.length = arity function)
    (hr : MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost)) :
    RunSafe original originalCount fuel function cells memory cell after cost :=
  run_sound original originalCount original_checked fuel function cells memory cell after cost hargs
    (by simpa only [original_erase] using hr)

end SubtreeProofs.Rust.MemoSource.Stack.Certificate
