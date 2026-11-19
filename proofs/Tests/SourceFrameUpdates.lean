import SubtreeProofs.Rust.SourceEvalFrameActions

namespace SourceFrameUpdateTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage

private def memory : Memory := [.number 7, .shared ⟨0, []⟩, .number 99]
private def world : World := ⟨memory, fun address =>
  if address = 0 then some .box else if address = 1 then some (.stack 20 0 0)
  else if address = 2 then some (.stack 10 0 0) else none,
  fun address => decide (address < 3)⟩
private def roots : Roots := fun slot => if slot = 0 then some ⟨2, 0⟩ else none
private def callerRoots : Roots := fun slot => if slot = 0 then some ⟨1, 0⟩ else none
private def emptyState : SourceEval.State := fun _ => .empty
private def caller : SourceEval.State := fun slot => if slot = 0 then .shared (.number 7) else .empty

private theorem well_formed : world.WellFormed := by
  constructor
  · intro a
    by_cases h₀ : a = 0
    · simp [world, memory, h₀]
    · by_cases h₁ : a = 1
      · simp [world, memory, h₁]
      · by_cases h₂ : a = 2
        · simp [world, memory, h₂]
        · simp [world, memory, h₀, h₁, h₂]
          omega
  · intro a hl
    exact (by simpa only [world, decide_eq_true_eq] using hl : a < 3)

private theorem active : Frame world 10 roots emptyState [2] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact ⟨_, [], rfl, rfl, .empty _, List.Subset.refl _⟩
  · simp only [roots, emptyState, hz, ite_false]

-- The context includes the suspended caller's resources. Its destination
-- binding is absent; adding the caller guards is an explicit checked weakening.
private theorem context : Frame world 10 (roots.set 0 none) (emptyState.set 0 .empty) [0, 1] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hz : slot = 0 <;> simp [Roots.set, roots, Partial.Locals.set, emptyState, hz]

private theorem caller_frame : Frame world 20 callerRoots caller [0, 1] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact ⟨_, [0], rfl, rfl, .shared (.shared (by rfl) (.number 7)), List.Subset.refl _⟩
  · simp only [callerRoots, caller, hz, ite_false]

private def written := world.write 2 (.number 42)
private def initialized := emptyState.set 0 (Slot.ofValue (.number 42))

private theorem assignment (call : SourceEval.Calls) :
    SourceEval.action call emptyState (.assign 0 (.use (.number 42))) = some (initialized, SourceEval.Cost.local 2) ∧
      world.writeStack 10 0 ⟨2, 0⟩ ([0, 1] ++ []) (.number 42) = some written ∧
      Frame written 10 roots initialized ([0, 1] ++ [] ++ [2]) ∧ written.memory.length = memory.length :=
  SourceEval.AddressedPrimitives.action_assign_number active well_formed call 0 42 (by decide +kernel)
    rfl rfl context (by simp)

example (call : SourceEval.Calls) : written.memory.length = memory.length := (assignment call).2.2.2
example : written.memory[2]? = some (.number 42) := rfl
example : written.classes 2 = some (.stack 10 0 0) := rfl
example : written.live 2 = true := rfl
example : ¬ Extends world.memory written.memory := by
  intro h
  have hh := h 2 (.number 99) (by rfl)
  change some (Cell.number 42) = some (.number 99) at hh
  cases hh

-- An actual write changes the existing storage cell, keeps its identity and
-- permits initialized address creation from the updated local frame.
example : ∃ pointer used, Storage.borrow written roots (.local 0) = some (.shared pointer) ∧
    Loan written pointer (.number 42) used ∧ used ++ [pointer.root] ⊆ [0, 1, 2] := by
  have h := (assignment (fun _ _ => none)).2.2.1
  apply h.borrow (.local 0)
  simp [initialized, Partial.Locals.read, splitPlace, Partial.Locals.set,
    Slot.read, Slot.get, Slot.materialize, Slot.ofValue]

private theorem caller_after : Frame written 20 callerRoots caller [0, 1] :=
  caller_frame.write (address := 2) (by simp) (.number 42)

-- Source storage-dead also releases a still-initialized reference local. Its
-- target stays alive, and no Box owner is lost; a retained shell cannot qualify.
example (call : SourceEval.Calls) :
    SourceEval.action call caller (.storageDead 0) = some (caller.set 0 .empty, SourceEval.Cost.local 1) ∧
      world.endStack 20 0 ⟨1, 0⟩ [0] = some (world.retire [1]) ∧
      Frame (world.retire [1]) 20 (callerRoots.set 0 none) (caller.set 0 .empty) [0] ∧
      (caller 0).dropWork.boxes = 0 ∧ (world.retire [1]).live 1 = false := by
  apply SourceEval.AddressedPrimitives.action_storageDead_nonowning caller_frame well_formed call 0 rfl
  · simp [caller, Slot.dropWork]
  · refine ⟨by simp [AliveOn, world], ?_⟩
    intro slot
    by_cases hz : slot = 0 <;> simp [Roots.set, callerRoots, Partial.Locals.set, caller, hz]
  · simp

example : (world.retire [1]).live 0 = true := rfl
example : (Slot.dropWork (.boxed .empty)).boxes ≠ 0 := by decide +kernel

example : ∃ pointer used, Storage.borrow written callerRoots (.deref (.local 0)) = some (.shared pointer) ∧
    Loan written pointer (.number 7) used ∧ used ++ [pointer.root] ⊆ [0, 1] :=
  caller_after.borrow _ (by simp [caller, Partial.Locals.read, splitPlace, Slot.read, Slot.get, Slot.ofValue, Slot.materialize])

-- Wrong storage class, caller identity, dead storage and alias conflicts all
-- reject the mutation; the raw write function is not mutation permission.
example : world.writeStack 10 0 ⟨0, 0⟩ [] (.number 42) = none := rfl
example : world.writeStack 11 0 ⟨2, 0⟩ [] (.number 42) = none := rfl
example : (world.retire [2]).writeStack 10 0 ⟨2, 0⟩ [] (.number 42) = none := rfl
example : world.writeStack 10 0 ⟨2, 0⟩ [2] (.number 42) = none := rfl
example : ¬ (2 : Nat) ∉ ([0, 1] ++ [2] : List Nat) := by simp

-- Ending storage consumes a source-empty local. The numeric value's earlier
-- operand step and general move/frame traces are separate contracts.
private theorem cleared : Frame written 10 roots emptyState [2] := by
  refine ⟨by simp [AliveOn, written, World.write, world], ?_⟩
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact ⟨_, [], rfl, rfl, .empty _, List.Subset.refl _⟩
  · simp only [roots, emptyState, hz, ite_false]
private theorem cleared_context : Frame written 10 (roots.set 0 none) (emptyState.set 0 .empty) [0, 1] :=
  context.write (address := 2) (by simp) (.number 42)

example (call : SourceEval.Calls) :
    SourceEval.action call emptyState (.storageDead 0) = some (emptyState.set 0 .empty, SourceEval.Cost.local 1) ∧
      written.endStack 10 0 ⟨2, 0⟩ [0, 1] = some (written.retire [2]) ∧
      Frame (written.retire [2]) 10 (roots.set 0 none) (emptyState.set 0 .empty) [0, 1] ∧
      (emptyState 0).dropWork = {} ∧ (written.retire [2]).live 2 = false :=
  SourceEval.AddressedPrimitives.action_storageDead cleared (well_formed.write _ _) call 0
    rfl rfl cleared_context (by simp)

example : Frame (written.retire [2]) 20 callerRoots caller [0, 1] := caller_after.retire (by simp)
example : written.endStack 10 0 ⟨2, 0⟩ [2] = none := rfl

-- Re-entering storage gets a fresh symbolic root/generation. The old root
-- stays dead, so an old reference is not revived by the new storage-live step.
private def ended := written.retire [2]
private def renewed := ended.allocate (.stack 10 0 1) (.node .tuple 0 [])
private def endedState := emptyState.set 0 .empty
private def endedRoots := roots.set 0 none
private theorem ended_frame : Frame ended 10 endedRoots endedState [0, 1] := cleared_context.retire (by simp)

example (call : SourceEval.Calls) :
    SourceEval.action call endedState (.storageLive 0) = some (endedState.set 0 .empty, SourceEval.Cost.local 1) ∧
      Frame renewed 10 (endedRoots.set 0 (some ⟨ended.memory.length, 1⟩)) (endedState.set 0 .empty)
        ([0, 1] ++ [] ++ [ended.memory.length]) ∧ renewed.WellFormed :=
  SourceEval.AddressedPrimitives.action_storageLive ended_frame ((well_formed.write _ _).retire _) call 0 1 rfl

example : renewed.live 2 = false ∧ renewed.live 3 = true := ⟨rfl, rfl⟩
example : renewed.classes 2 = some (.stack 10 0 0) ∧ renewed.classes 3 = some (.stack 10 0 1) := ⟨rfl, rfl⟩

-- Protecting only an outer reference permits corruption of a nested stack
-- target. The full graph-derived guard rejects the same write.
private def nested : World := { world with classes := fun address => if address = 0 then some (.stack 30 0 0) else world.classes address }
example : nested.writeStack 30 0 ⟨0, 0⟩ [1] (.number 8) = some (nested.write 0 (.number 8)) := rfl
example : nested.writeStack 30 0 ⟨0, 0⟩ [0, 1] (.number 8) = none := rfl
example : ¬ Retains nested.memory (nested.write 0 (.number 8)).memory [0, 1] := by
  intro h
  have hh := h 0 (by simp) (.number 7) (by rfl)
  change some (Cell.number 8) = some (.number 7) at hh
  cases hh


-- The complete owner ledger also transports across an unrelated local write;
-- graph preservation is not limited to shared snapshot readback.
example : Rep written.memory (.owned 0) (.boxed (.number 7)) [0] := by
  have hg : PartialGraph world.memory (.owned 0) (.boxed (.number 7)) [0] :=
    .owned (by rfl) (.number 7)
  have ho : Rep world.memory (.owned 0) (.boxed (.number 7)) [0] :=
    .owned (by rfl) (.number 7)
  exact hg.owner_transport ho (world.write_preserves (guards := [0]) (address := 2) (by simp) (.number 42)).reads

end SourceFrameUpdateTests
