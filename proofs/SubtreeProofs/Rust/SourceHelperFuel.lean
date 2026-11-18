module

public import SubtreeProofs.Rust.SourceEvalDeterminism
public import SubtreeProofs.Rust.SourceHeapFuel
public import SubtreeProofs.Rust.SourceHelperTotality

/-! Actual helpers preserve completed worlds/packets/full costs at larger call
fuel. Independent input types therefore give joint fuel/readback thresholds with
one stable completed result, rather than a readback bound varying with fuel. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap Partial Partial.Addressed Storage

theorem finish_extends {first second : Option (Cell × Memory × LookupSource.Cost)}
    (hc : ∀ result, first = some result → second = some result)
    {budget : Nat} {world final : World} {packet : ValueCell} {cost : SourceEval.Cost}
    (h : finish budget world first = some (final, packet, cost)) :
    finish budget world second = some (final, packet, cost) := by
  cases first with
  | none => cases h
  | some result => simpa only [hc result rfl] using h

theorem execute_fuel_enlarge {small large budget : Nat} (bound : small ≤ large)
    {world final : World} {function : Function} {packets : List ValueCell} {packet : ValueCell} {cost : SourceEval.Cost}
    (h : execute small budget world function packets = some (final, packet, cost)) :
    execute large budget world function packets = some (final, packet, cost) := by
  cases function with
  | copyWord | compare | copyResult | lookup =>
    apply finish_extends (fun result hr => ?_) h
    rcases result with ⟨cell, memory, cost⟩
    exact Heap.run_fuel_enlarge LookupSource.Program.body bound _ _ _ _ _ _ hr
  | concatenate | insert =>
    apply finish_extends (fun result hr => ?_) h
    rcases result with ⟨cell, memory, cost⟩
    exact MemoSource.Heap.run_fuel_enlarge MemoSource.Program.body bound _ _ _ _ _ _ hr
  | boxNew =>
    cases small with
    | zero => cases h
    | succ small => cases large with
      | zero => omega
      | succ large =>
        cases packets with
        | nil => cases h
        | cons packet rest => cases rest with
          | nil => rcases packet with ⟨cell, value⟩; exact h
          | cons _ _ => cases h
  | checkedAdd =>
    cases small with
    | zero => cases h
    | succ small => cases large with
      | zero => omega
      | succ large =>
        cases packets with
        | nil => cases h
        | cons first rest => cases rest with
          | nil => rcases first with ⟨left, value⟩; cases left <;> cases h
          | cons second rest => cases rest with
            | cons _ _ =>
              rcases first with ⟨left, leftValue⟩
              rcases second with ⟨right, rightValue⟩
              cases left <;> cases right <;> cases h
            | nil =>
              rcases first with ⟨left, leftValue⟩
              rcases second with ⟨right, rightValue⟩
              cases left <;> cases right <;> exact h
  | chooseLonger | evaluate | maximum => cases h

theorem typed_stable_bounds {world : World} {function : Function} {packets : List ValueCell}
    (helper : Recursive.interpreted function = false) (hw : world.WellFormed)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world function packets) :
    ∃ minimumFuel minimumBudget final packet cost, ∀ fuel budget,
      minimumFuel ≤ fuel → minimumBudget ≤ budget →
        execute fuel budget world function packets = some (final, packet, cost) := by
  obtain ⟨minimumFuel, ready⟩ := typed_ready_exists helper hp ht
  obtain ⟨minimumBudget, final, packet, cost, run⟩ := ready.executes hw hp
  exact ⟨minimumFuel, minimumBudget, final, packet, cost, fun _ _ hf hb =>
    execute_budget_enlarge hb (execute_fuel_enlarge hf run)⟩

theorem typed_owned_stable_bounds {world : World} {function : Function} {packets : List ValueCell}
    (helper : Recursive.interpreted function = false) (hw : world.WellFormed)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world function packets) (guards : List Nat) (callers : List Activation)
    (hc : ∀ a ∈ callers, a.Valid world) (hl : AliveOn world.live guards)
    (owners external : List Nat) (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (hf : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (coverage : BoxCoverage world (owners ++ (callerOwners world callers ++ external))) :
    ∃ minimumFuel minimumBudget final packet cost output,
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      Footprint final.memory packet.1 output ∧
      OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (output ++ (callerOwners final callers ++ external)) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        callee fuel budget world guards callers function packets = some (final, packet, cost) ∧
        SourceEval.run SourceEval.Certificate.original.body fuel function (packets.map Prod.snd) = some (packet.2, cost) := by
  obtain ⟨minimumFuel, minimumBudget, final, packet, cost, output, run, source, readable, wf, keeps, foot, frame, covered⟩ :=
    typed_owned_total helper hw hp ht guards callers hc hl owners external ho hf coverage
  refine ⟨minimumFuel, minimumBudget, final, packet, cost, output, readable, wf, keeps, foot, frame, covered, ?_⟩
  intro fuel budget fuelBound budgetBound
  have larger := execute_budget_enlarge budgetBound (execute_fuel_enlarge fuelBound run)
  exact ⟨larger, SourceEval.run_extends SourceEval.Certificate.original.body fuelBound source⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
