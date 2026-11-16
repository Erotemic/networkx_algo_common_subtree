module

public import Std.WP.Monad.Instances
public import Std.WP.Monad.Sound
public import SubtreeProofs.Rust.LookupSourceMutation

/-!
# Std.WP adapter for the reified lookup execution

The interpreter, rather than the result specification, supplies the work.
This adapter preserves its successful values, instruction counts, and packet
counts in an explicit state. It adds no Rust or heap adequacy claim. Insufficient
fuel and unsupported executions are errors outside the successful-run contract;
no error-path resource bound is asserted.
-/

@[expose] public section

open scoped Lean.Order
open Std.WP

namespace ResourceCostAudit.LookupSourceWP

open SubtreeProofs.Rust
open LookupSource
open verified_ordered_core

/-- Execute the existing operational semantics and accumulate all its work.
The counter is observed only by specifications, never by source control flow. -/
def call (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) : EStateM Unit Cost Value := fun initial =>
  match run body fuel function args with
  | none => .error () initial
  | some (value, cost) => .ok value (initial.plus cost)

/-- A successful WP contract is exactly a successful operational run with
the same result and complete accumulated cost. -/
theorem call_wp_iff (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) (post : Value → Cost → Prop) (initial : Cost) :
    Std.WP.wp (call body fuel function args) post (fun _ _ => False) initial ↔
      ∃ value cost, run body fuel function args = some (value, cost) ∧
        post value (initial.plus cost) := by
  simp only [Std.WP.WP.wp, Std.WP.WP.wpTrans]
  cases h : run body fuel function args with
  | none => simp [call, h]
  | some pair =>
    rcases pair with ⟨value, cost⟩
    simp [call, h]

/-- Transfer a local interpreter contract without replacing execution by
its independently specified answer. -/
theorem call_wp_of_run (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) {value : Value} {cost : Cost}
    (hr : run body fuel function args = some (value, cost))
    (post : Value → Cost → Prop) (initial : Cost)
    (hp : post value (initial.plus cost)) :
    Std.WP.wp (call body fuel function args) post (fun _ _ => False) initial :=
  (call_wp_iff body fuel function args post initial).2 ⟨value, cost, hr, hp⟩

/-- Lookup returns the independent first hit and accumulates the exact
operational packet vector, including structural comparisons and witness copy.
Duplicate keys need no uniqueness premise. -/
theorem lookup_wp (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (initial : Cost) :
    Std.WP.wp (call Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left),
        .reference (encodeWord right)])
      (fun value final =>
        value = encodeOption (MemoizedOrderedSolver.findResult table left right) ∧
        final.events = initial.events.plus (LookupEvents.lookup table left right).2 ∧
        final.steps ≤ initial.steps + 256 * (LookupEvents.lookup table left right).2.units)
      (fun _ _ => False) initial := by
  obtain ⟨cost, hr, hc⟩ := lookup_source table left right fuel hf
  apply call_wp_of_run _ _ _ _ hr
  refine ⟨?_, ?_, ?_⟩
  · rw [LookupEvents.lookup_value]
  · exact congrArg (initial.events.plus) hc
  · have hb := program_source_bound hr
    rw [hc] at hb
    exact Nat.add_le_add_left hb initial.steps

/-- The recursive structural scan uses the same adapter as lookup.
Short-circuit traversal counts come from its operational theorem. -/
theorem compare_wp (left right : BalancedWord) (fuel : Nat)
    (hf : wordHeight left ≤ fuel) (initial : Cost) :
    Std.WP.wp (call Program.body fuel .compare
      [.reference (encodeWord left), .reference (encodeWord right)])
      (fun value final =>
        value = .boolean (decide (left = right)) ∧
        final.events = initial.events.plus
          ⟨0, (LookupEvents.compare left right).2, 0, 0, 0⟩ ∧
        final.steps ≤ initial.steps + 256 * (LookupEvents.compare left right).2)
      (fun _ _ => False) initial := by
  obtain ⟨cost, hr, hc⟩ := compare_source left right fuel hf
  apply call_wp_of_run _ _ _ _ hr
  refine ⟨?_, congrArg (initial.events.plus) hc, ?_⟩
  · rw [LookupEvents.compare_value]
  · have hb := program_source_bound hr
    rw [hc] at hb
    simp only [LookupEvents.Events.units, Nat.zero_add, Nat.add_zero] at hb
    exact Nat.add_le_add_left hb initial.steps

/-- Complete owned copying carries the same allocation and constructor
packets through the WP state. -/
theorem copy_wp (word : BalancedWord) (fuel : Nat)
    (hf : wordHeight word ≤ fuel) (initial : Cost) :
    Std.WP.wp (call Program.body fuel .copyWord [.reference (encodeWord word)])
      (fun value final => value = encodeWord word ∧
        final.events = initial.events.plus (LookupEvents.copy word).2 ∧
        final.steps ≤ initial.steps + 256 * (LookupEvents.copy word).2.units)
      (fun _ _ => False) initial := by
  obtain ⟨cost, hr, hc⟩ := copy_source word fuel hf
  apply call_wp_of_run _ _ _ _ hr
  refine ⟨rfl, congrArg (initial.events.plus) hc, ?_⟩
  have hb := program_source_bound hr
  rw [hc] at hb
  exact Nat.add_le_add_left hb initial.steps

theorem copyResult_wp (result : CommonEmbedding) (fuel : Nat)
    (hf : wordHeight result.word + 1 ≤ fuel) (initial : Cost) :
    Std.WP.wp (call Program.body fuel .copyResult [.reference (encodeResult result)])
      (fun value final => value = encodeResult result ∧
        final.events = initial.events.plus (LookupEvents.copyResult result).2 ∧
        final.steps ≤ initial.steps + 256 * (LookupEvents.copyResult result).2.units)
      (fun _ _ => False) initial := by
  obtain ⟨cost, hr, hc⟩ := copyResult_source result fuel hf
  apply call_wp_of_run _ _ _ _ hr
  refine ⟨rfl, congrArg (initial.events.plus) hc, ?_⟩
  have hb := program_source_bound hr
  rw [hc] at hb
  exact Nat.add_le_add_left hb initial.steps

/-- Binding calls threads the full prior work into the second call.
The argument of the second source call may depend on the first result. -/
theorem bind_run (body : Function → Code) (fuel : Nat)
    (first second : Function) (args : List Value) (next : Value → List Value)
    {value₁ value₂ : Value} {cost₁ cost₂ : Cost}
    (h₁ : run body fuel first args = some (value₁, cost₁))
    (h₂ : run body fuel second (next value₁) = some (value₂, cost₂))
    (initial : Cost) :
    EStateM.run (do
      let value ← call body fuel first args
      call body fuel second (next value)) initial =
        .ok value₂ ((initial.plus cost₁).plus cost₂) := by
  simp [EStateM.run, call, h₁, h₂, bind, EStateM.bind]

/-- The actual compiled source mutation fails the old zero-comparison WP
contract, although it still returns the same independent empty-table result. -/
theorem extra_compare_rejects_old_wp :
    ¬Std.WP.wp (call ExtraCompare.body 3 .lookup
      [.reference (encodeTable .Empty), .reference (encodeWord .Empty),
        .reference (encodeWord .Empty)])
      (fun value final => value = encodeOption none ∧ final.events.compareNodes = 0)
      (fun _ _ => False) ({} : Cost) := by
  intro hw
  obtain ⟨cost, hr, hc⟩ := extra_compare_execution
  obtain ⟨value, actual, ha, hp⟩ := (call_wp_iff _ _ _ _ _ _).1 hw
  rw [hr] at ha
  cases ha
  have hn := hp.2
  simp [Cost.plus, LookupEvents.Events.plus, hc] at hn

#check @call_wp_iff
#check @lookup_wp
#check @compare_wp
#check @copy_wp
#check @copyResult_wp
#check @extra_compare_rejects_old_wp

#print axioms call_wp_iff
#print axioms lookup_wp
#print axioms compare_wp
#print axioms copy_wp
#print axioms copyResult_wp
#print axioms bind_run
#print axioms extra_compare_rejects_old_wp

end ResourceCostAudit.LookupSourceWP
