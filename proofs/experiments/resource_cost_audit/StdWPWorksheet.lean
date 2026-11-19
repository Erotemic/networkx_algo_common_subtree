module

public import Std.WP.Monad.Instances
public import Std.WP.Monad.Sound
public import SubtreeProofs.Rust.MemoizedOrderedSolver

/-!
G0 API worksheet, not a source-cost theorem or a new verification framework.
The existing Std.WP instance can state both the independent first-hit lookup
postcondition and a bound on an explicitly represented counter state. It does
not establish that this state counts any Rust operation. G1 must supply that
semantics and its adequacy before using such a contract as a runtime result.
-/
@[expose] public section

open scoped Lean.Order
open Std.WP

namespace ResourceCostAudit

open verified_ordered_core
open SubtreeProofs.Rust.MemoizedOrderedSolver

/-- The installed WP interpretation expresses the intended result/counter
contract without another predicate-transformer implementation. Any program
passed here still needs an independent source/event correspondence theorem. -/
theorem lookup_wp_iff_run
    (program : EStateM Empty Nat (Option CommonEmbedding))
    (table : MemoTable) (left right : BalancedWord) (budget : Nat) :
    Std.WP.wp program
      (fun result count => result = findResult table left right ∧ count ≤ budget)
      (fun _ _ => False) 0 ↔
      ∃ result count, EStateM.run program 0 = .ok result count ∧
        result = findResult table left right ∧ count ≤ budget := by
  simp only [Std.WP.WP.wp, Std.WP.WP.wpTrans]
  cases h : program 0 with
  | ok result count => simp [EStateM.run, h]
  | error e _ => cases e

end ResourceCostAudit
