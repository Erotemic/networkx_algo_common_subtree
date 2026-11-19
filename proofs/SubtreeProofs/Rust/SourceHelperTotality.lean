module

public import SubtreeProofs.Rust.SourceHelperReadiness
public import SubtreeProofs.Rust.SourceReadbackBudget

/-! All eight actual helper callees have some sufficient call fuel and ghost
readback budget on independently typed readable inputs. This discharges helper
existence only; interpreted evaluator entry, dynamic guards and teardown retain
separate obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem finish_budget_enlarge {small large : Nat} (bound : small ≤ large)
    {world final : World} {raw : Option (Cell × Memory × LookupSource.Cost)}
    {packet : ValueCell} {cost : SourceEval.Cost}
    (h : finish small world raw = some (final, packet, cost)) :
    finish large world raw = some (final, packet, cost) := by
  cases raw with
  | none => cases h
  | some triple =>
    rcases triple with ⟨cell, memory, oldCost⟩
    cases hp : readPacket small (world.boxSuffix memory) cell with
    | none => simp [finish, hp] at h
    | some found =>
      have larger := readPacket_enlarge bound hp
      simpa only [finish, Bind.bind, Option.bind, larger] using
        (show some (world.boxSuffix memory, found, Legacy.costMap oldCost) = some (final, packet, cost) by
          simpa only [finish, Bind.bind, Option.bind, hp] using h)

theorem execute_budget_enlarge {small large fuel : Nat} (bound : small ≤ large)
    {world final : World} {function : Function} {packets : List ValueCell} {packet : ValueCell} {cost : SourceEval.Cost}
    (h : execute fuel small world function packets = some (final, packet, cost)) :
    execute fuel large world function packets = some (final, packet, cost) := by
  cases function <;> first
    | exact finish_budget_enlarge bound h
    | exact h

theorem Ready.executes {fuel : Nat} {world : World} {function : Function} {packets : List ValueCell}
    (ready : Ready fuel function packets) (hw : world.WellFormed)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) :
    ∃ budget final packet cost, execute fuel budget world function packets = some (final, packet, cost) := by
  cases ready with
  | copyWord word pointer depth =>
    obtain ⟨cell, memory, cost, run, _⟩ := copy_total word fuel (valueDepth (encodeWord word)) depth hw pointer
      (hp (.shared pointer, .reference (encodeWord word)) (by simp)) (Nat.le_refl _)
    exact ⟨_, _, _, _, run⟩
  | compare left right pl pr depth =>
    obtain ⟨memory, cost, run, _⟩ := compare_total left right fuel 1 depth hw pl pr
      (hp (.shared pl, .reference (encodeWord left)) (by simp)) (hp (.shared pr, .reference (encodeWord right)) (by simp)) (Nat.le_refl _)
    exact ⟨_, _, _, _, run⟩
  | copyResult result pointer depth =>
    obtain ⟨cell, memory, cost, run, _⟩ := copyResult_total result fuel (valueDepth (encodeResult result)) depth hw pointer
      (hp (.shared pointer, .reference (encodeResult result)) (by simp)) (Nat.le_refl _)
    exact ⟨_, _, _, _, run⟩
  | lookup table left right pt pl pr depth =>
    obtain ⟨cell, memory, cost, run, _⟩ := lookup_total table left right fuel
      (valueDepth (encodeOption (LookupEvents.lookup table left right).1)) depth hw pt pl pr
      (hp (.shared pt, .reference (encodeTable table)) (by simp)) (hp (.shared pl, .reference (encodeWord left)) (by simp)) (hp (.shared pr, .reference (encodeWord right)) (by simp)) (Nat.le_refl _)
    exact ⟨_, _, _, _, run⟩
  | concatenate left right pl pr depth =>
    obtain ⟨cell, memory, cost, run, _⟩ := concatenate_total left right fuel
      (valueDepth (encodeWord (OrderedSolver.appendWord left right))) depth hw pl pr
      (hp (.shared pl, .reference (encodeWord left)) (by simp)) (hp (.shared pr, .reference (encodeWord right)) (by simp)) (Nat.le_refl _)
    exact ⟨_, _, _, _, run⟩
  | insert table left right result tc pl pr pc depth =>
    obtain ⟨cell, memory, cost, old, owners, run, _⟩ := insert_total table left right result fuel
      (valueDepth (encodeTable (.Entry ⟨left, right, result⟩ table))) depth hw tc pl pr pc
      (hp (tc, encodeTable table) (by simp)) (hp (.shared pl, .reference (encodeWord left)) (by simp)) (hp (.shared pr, .reference (encodeWord right)) (by simp)) (hp (.shared pc, .reference (encodeResult result)) (by simp)) (Nat.le_refl _)
    exact ⟨_, _, _, _, run⟩
  | boxNew cell value positive =>
    cases fuel with
    | zero => omega
    | succ fuel => exact ⟨0, _, _, _, (boxNew_total fuel hw (hp (cell, value) (by simp))).1⟩
  | checkedAdd left right positive hl hr =>
    cases fuel with
    | zero => omega
    | succ fuel => exact ⟨0, _, _, _, (checkedAdd_total fuel hw left right hl hr).1⟩

theorem typed_total {world : World} {function : Function} {packets : List ValueCell}
    (helper : Recursive.interpreted function = false) (hw : world.WellFormed)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world function packets) (guards : List Nat) (callers : List Activation)
    (hc : ∀ a ∈ callers, a.Valid world) (hl : AliveOn world.live guards) :
    ∃ fuel budget final packet cost,
      callee fuel budget world guards callers function packets = some (final, packet, cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel function (packets.map Prod.snd) = some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards := by
  obtain ⟨fuel, ready⟩ := typed_ready_exists helper hp ht
  obtain ⟨budget, final, packet, cost, run⟩ := ready.executes hw hp
  exact ⟨fuel, budget, final, packet, cost, run,
    callee_respects fuel budget world guards callers function packets final packet cost hw hp hc hl ready run⟩

theorem typed_owned_total {world : World} {function : Function} {packets : List ValueCell}
    (helper : Recursive.interpreted function = false) (hw : world.WellFormed)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world function packets) (guards : List Nat) (callers : List Activation)
    (hc : ∀ a ∈ callers, a.Valid world) (hl : AliveOn world.live guards)
    (owners external : List Nat) (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (hf : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (coverage : BoxCoverage world (owners ++ (callerOwners world callers ++ external))) :
    ∃ fuel budget final packet cost output,
      callee fuel budget world guards callers function packets = some (final, packet, cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel function (packets.map Prod.snd) = some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      Footprint final.memory packet.1 output ∧
      OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (output ++ (callerOwners final callers ++ external)) := by
  obtain ⟨fuel, budget, final, packet, cost, run, source, readable, wf, keeps⟩ :=
    typed_total helper hw hp ht guards callers hc hl
  obtain ⟨output, foot, frame, covered⟩ := callee_owns fuel budget world guards callers function packets final packet cost
    owners external hw hc hp hl ht ho hf coverage run
  exact ⟨fuel, budget, final, packet, cost, output, run, source, readable, wf, keeps, foot, frame, covered⟩

theorem typed_sufficient_fuel {world : World} {function : Function} {packets : List ValueCell}
    (helper : Recursive.interpreted function = false) (hw : world.WellFormed)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world function packets) :
    ∃ minimumFuel, ∀ fuel, minimumFuel ≤ fuel →
      ∃ minimumBudget final packet cost, ∀ budget, minimumBudget ≤ budget →
        execute fuel budget world function packets = some (final, packet, cost) := by
  obtain ⟨minimumFuel, ready⟩ := typed_ready_exists helper hp ht
  refine ⟨minimumFuel, fun fuel bound => ?_⟩
  obtain ⟨minimumBudget, final, packet, cost, run⟩ := (ready.enlarge bound).executes hw hp
  exact ⟨minimumBudget, final, packet, cost, fun _ bound => execute_budget_enlarge bound run⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
