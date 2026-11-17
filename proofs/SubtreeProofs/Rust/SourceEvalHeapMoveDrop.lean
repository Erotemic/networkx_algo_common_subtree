module

public import SubtreeProofs.Rust.SourcePartialHeapLocals
public import SubtreeProofs.Rust.SourcePartialHeapSpatial
public import SubtreeProofs.Rust.SourceEvalMachine

/-! The existing expanded-source move/drop primitives consume addressed
partial-local representations with unchanged source costs. Logical retirement
has explicit live-owner and guarded-address premises. Complete evaluator heap
execution, local borrow creation and Rust destructor interpretation are separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.AddressedPrimitives

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed

theorem operand_move {memory : Heap.Memory} {raw : Heap.Locals} {state after : State} {owners : OwnerState}
    (h : EnvRep memory raw state owners) {place : Place} {value : Value}
    (hr : operand state (.move place) = some (value, after)) :
    ∃ root moved movedOwners remainingOwners,
      raw (splitPlace place).1 = some root ∧ ownedProjection memory root (splitPlace place).2 = some moved ∧
      Heap.Represents memory moved value ∧ Heap.Footprint memory moved movedOwners ∧
      EnvRep memory raw after (owners.set (splitPlace place).1 remainingOwners) ∧
      (owners (splitPlace place).1).Perm (movedOwners ++ remainingOwners) := by
  exact h.move hr

theorem box_new (body : Function → Code) (fuel : Nat) {memory : Heap.Memory} {cell : Heap.Cell}
    {value : Value} {owners : List Nat} (h : Rep memory cell (Slot.ofValue value) owners) :
    run body (fuel + 1) .boxNew [value] = some (.boxed value, Cost.entry .boxNew) ∧
      Rep (Heap.alloc memory cell).2 (Heap.alloc memory cell).1 (Slot.ofValue (.boxed value))
        (owners ++ [memory.length]) ∧
      Heap.Extends memory (Heap.alloc memory cell).2 ∧
      memory[memory.length]? = none ∧ (Heap.alloc memory cell).2.length = memory.length + 1 :=
  ⟨rfl, by simpa only [Slot.ofValue] using h.alloc,
    Heap.Extends.append memory [cell], (Heap.alloc_fresh memory cell).1, (Heap.alloc_fresh memory cell).2.2⟩


theorem action_drop {memory : Heap.Memory} {raw : Heap.Locals} {state : State} {owners : OwnerState}
    (h : EnvRep memory raw state owners) (call : Calls) (slot : Nat) :
    destroyLocal memory (raw slot) (state slot) = some (owners slot, (state slot).dropWork) ∧
      action call state (.drop slot) = some (state.set slot .empty, Cost.local 1 (state slot).dropWork) ∧
      EnvRep memory (raw.set slot none) (state.set slot .empty) (owners.set slot []) ∧
      (owners slot).length = (state slot).dropWork.boxes :=
  ⟨(h slot).destroy, SourceEval.action_drop call state slot, h.clear slot, (h slot).boxes⟩

theorem action_drop_retire {memory : Heap.Memory} {raw : Heap.Locals} {state : State} {owners : OwnerState}
    (h : EnvRep memory raw state owners) (call : Calls) (slot : Nat) {live : Live}
    (hl : AliveOn live (owners slot)) (hn : (owners slot).Nodup)
    {guarded : List Nat} (hs : ∀ address ∈ guarded, address ∉ owners slot) (hp : AliveOn live guarded) :
    destroyLocal memory (raw slot) (state slot) = some (owners slot, (state slot).dropWork) ∧
      action call state (.drop slot) = some (state.set slot .empty, Cost.local 1 (state slot).dropWork) ∧
      EnvRep memory (raw.set slot none) (state.set slot .empty) (owners.set slot []) ∧
      (owners slot).length = (state slot).dropWork.boxes ∧ (owners slot).Nodup ∧
      (∀ address ∈ owners slot, live address = true ∧ retire live (owners slot) address = false) ∧
      AliveOn (retire live (owners slot)) guarded := by
  have hd := action_drop h call slot
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, hn,
    fun address ha => ⟨hl address ha, retire_member live ha⟩, retire_preserves hs hp⟩

/-- Source drop work includes visits exactly once; the addressed traversal
selects the concrete owners corresponding to its diagnostic Box count. -/
theorem action_drop_cost {memory : Heap.Memory} {raw : Heap.Locals} {state : State} {owners : OwnerState}
    (h : EnvRep memory raw state owners) (call : Calls) (slot : Nat) :
    ∃ cost, action call state (.drop slot) = some (state.set slot .empty, cost) ∧
      destroyLocal memory (raw slot) (state slot) = some (owners slot, cost.destroyed) ∧
      cost.work.steps = 1 + cost.destroyed.visits ∧ cost.destroyed.boxes = (owners slot).length := by
  have hd := action_drop h call slot
  exact ⟨Cost.local 1 (state slot).dropWork, hd.2.1, hd.1, rfl, hd.2.2.2.symm⟩

end SubtreeProofs.Rust.SourceEval.AddressedPrimitives
