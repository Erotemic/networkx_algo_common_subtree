module

public import SubtreeProofs.Rust.LookupSourceFrontend
public import SubtreeProofs.Rust.Generated.LookupSourceInput
public import SubtreeProofs.Rust.Generated.LookupSourceExtraCompareInput
public import SubtreeProofs.Rust.LookupSourceMutation

import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Data.Ord.String
import all Init.Control.Except
import all SubtreeProofs.Rust.LookupSourceFrontend
import all SubtreeProofs.Rust.LookupSourceControl
import all SubtreeProofs.Rust.LookupSource
import all SubtreeProofs.Rust.Generated.LookupSourceInput
import all SubtreeProofs.Rust.Generated.LookupSourceExtraCompareInput

/-! Kernel-checked source-control certificates for both real extractions.
The JSON snapshots are data from pinned Charon; the external Python reifier is
not trusted to preserve the supported control/primitive syntax. Exact execution
and cost transfer use the proved normalizer, not equality of final values alone.
This still uses snapshot references and the declared primitive semantics;
typed heap/alias/lifetime and Rust execution adequacy remain open. -/

@[expose] public section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

namespace SubtreeProofs.Rust.LookupSource.Certificate

def decoded (json : Lean.Json) : Frontend.Program :=
  (Frontend.read json 512).toOption.getD ⟨.done, .done, .done, .done⟩

def original : Frontend.Program := decoded Input.Program.source
def mutant : Frontend.Program := decoded Input.ExtraCompare.source

theorem original_read : Frontend.read Input.Program.source 512 = .ok original := by with_unfolding_all rfl

theorem mutant_read : Frontend.read Input.ExtraCompare.source 512 = .ok mutant := by with_unfolding_all rfl

theorem original_lower (function : Function) :
    Control.lower (original.body function) = some (Program.body function) := by
  cases function <;> with_unfolding_all rfl

theorem mutant_lower (function : Function) :
    Control.lower (mutant.body function) = some (ExtraCompare.body function) := by
  cases function <;> with_unfolding_all rfl

theorem original_checked : Frontend.check Input.Program.source 512 Program.body = true :=
  (Frontend.check_iff _ _ _).mpr ⟨original, original_read, original_lower⟩

theorem mutant_checked : Frontend.check Input.ExtraCompare.source 512 ExtraCompare.body = true :=
  (Frontend.check_iff _ _ _).mpr ⟨mutant, mutant_read, mutant_lower⟩

/-- The source-level extra comparison cannot pass a certificate for the old
normal form even though it returns the same answer on the empty-table case. -/
theorem mutant_rejects_original : Frontend.check Input.ExtraCompare.source 512 Program.body = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  obtain ⟨program, hr, hl⟩ := (Frontend.check_iff _ _ _).mp hc
  rw [mutant_read] at hr
  cases hr
  have he := Option.some.inj ((mutant_lower .lookup).symm.trans (hl .lookup))
  have hbranch := congrArg (fun code => match code with
    | .step _ (.branch ..) => true
    | _ => false) he
  change false = true at hbranch
  cases hbranch

theorem original_run (fuel : Nat) (function : Function) (args : List Value) :
    Control.run original.body fuel function args = run Program.body fuel function args :=
  Control.run_lower original.body Program.body original_lower fuel function args

theorem mutant_run (fuel : Nat) (function : Function) (args : List Value) :
    Control.run mutant.body fuel function args = run ExtraCompare.body fuel function args :=
  Control.run_lower mutant.body ExtraCompare.body mutant_lower fuel function args

/-- Original instruction/event bounds now apply to the checked source-control
execution, with the original snapshot primitive boundary explicitly retained. -/
theorem original_run_bound {fuel : Nat} {function : Function} {args : List Value}
    {value : Value} {cost : Cost}
    (hr : Control.run original.body fuel function args = some (value, cost)) :
    cost.steps ≤ 256 * cost.events.units := by
  rw [original_run] at hr
  exact program_source_bound hr

open verified_ordered_core in
theorem mutant_violates_old_comparison_budget :
    ∃ cost, Control.run mutant.body 3 .lookup
      [.reference (encodeTable .Empty), .reference (encodeWord .Empty),
        .reference (encodeWord .Empty)] = some (encodeOption none, cost) ∧
      ¬cost.events.compareNodes ≤ MemoizedOrderedSolver.memoLength .Empty *
        ((2 * (OrderedSolver.toDyck .Empty).semilength + 1) +
          (2 * (OrderedSolver.toDyck .Empty).semilength + 1)) := by
  rw [mutant_run]
  exact extra_compare_violates_old_bound

end SubtreeProofs.Rust.LookupSource.Certificate
