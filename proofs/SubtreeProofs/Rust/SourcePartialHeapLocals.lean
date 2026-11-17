module

public import SubtreeProofs.Rust.SourcePartialHeapMoves
public import SubtreeProofs.Rust.SourcePartialHeapDrop

/-! Addressed local values and per-local complete owner lists. Moves retain
stored data and update initialization/ownership; clears remove local storage
from this view. Allocation, spatial separation and live loans are separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

inductive LocalRep (memory : Memory) : Option Cell → Slot → List Nat → Prop where
  | empty : LocalRep memory none .empty []
  | stored {cell : Cell} {part : Slot} {owners : List Nat} :
      Rep memory cell part owners → LocalRep memory (some cell) part owners

theorem LocalRep.none_inv {memory : Memory} {part : Slot} {owners : List Nat}
    (h : LocalRep memory none part owners) : part = .empty ∧ owners = [] := by cases h; exact ⟨rfl, rfl⟩

theorem LocalRep.some_inv {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
    (h : LocalRep memory (some cell) part owners) : Rep memory cell part owners := by cases h; assumption

abbrev OwnerState := Nat → List Nat

def OwnerState.set (owners : OwnerState) (slot : Nat) (value : List Nat) : OwnerState := fun index =>
  if index = slot then value else owners index

def EnvRep (memory : Memory) (raw : LookupSource.Heap.Locals) (state : Partial.Locals) (owners : OwnerState) : Prop :=
  ∀ slot, LocalRep memory (raw slot) (state slot) (owners slot)

theorem EnvRep.store {memory : Memory} {raw : LookupSource.Heap.Locals} {state : Partial.Locals} {owners : OwnerState}
    (h : EnvRep memory raw state owners) (slot : Nat) {cell : Option Cell} {part : Slot} {own : List Nat}
    (hr : LocalRep memory cell part own) :
    EnvRep memory (raw.set slot cell) (state.set slot part) (owners.set slot own) := by
  intro index
  by_cases hi : index = slot
  · subst index
    simpa only [LookupSource.Heap.Locals.set, Partial.Locals.set, OwnerState.set, ite_true] using hr
  · simpa only [LookupSource.Heap.Locals.set, Partial.Locals.set, OwnerState.set, hi, ite_false] using h index

theorem EnvRep.clear {memory : Memory} {raw : LookupSource.Heap.Locals} {state : Partial.Locals} {owners : OwnerState}
    (h : EnvRep memory raw state owners) (slot : Nat) :
    EnvRep memory (raw.set slot none) (state.set slot .empty) (owners.set slot []) := h.store slot .empty

theorem EnvRep.remask {memory : Memory} {raw : LookupSource.Heap.Locals} {state : Partial.Locals} {owners : OwnerState}
    (h : EnvRep memory raw state owners) {slot : Nat} {cell : Cell} (hc : raw slot = some cell)
    {part : Slot} {own : List Nat} (hr : Rep memory cell part own) :
    EnvRep memory raw (state.set slot part) (owners.set slot own) := by
  intro index
  by_cases hi : index = slot
  · subst index
    simpa only [Partial.Locals.set, OwnerState.set, ite_true, hc] using LocalRep.stored hr
  · simpa only [Partial.Locals.set, OwnerState.set, hi, ite_false] using h index

theorem take_empty (path : List Projection) : Slot.empty.take path = none := by
  cases path with
  | nil => simp only [Slot.take, Slot.materialize, bind, Option.bind]
  | cons projection rest => cases projection <;> rfl

theorem EnvRep.move {memory : Memory} {raw : LookupSource.Heap.Locals} {state after : Partial.Locals}
    {owners : OwnerState} (h : EnvRep memory raw state owners) {place : Place} {value : Value}
    (ht : state.move place = some (value, after)) :
    ∃ root moved movedOwners remainingOwners,
      raw (splitPlace place).1 = some root ∧ ownedProjection memory root (splitPlace place).2 = some moved ∧
      Represents memory moved value ∧ Footprint memory moved movedOwners ∧
      EnvRep memory raw after (owners.set (splitPlace place).1 remainingOwners) ∧
      (owners (splitPlace place).1).Perm (movedOwners ++ remainingOwners) := by
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [Partial.Locals.move, hp] at ht
  cases hs : (state slot).take path with
  | none => simp [hs] at ht
  | some pair =>
    rcases pair with ⟨result, remaining⟩
    simp only [hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    cases hc : raw slot with
    | none =>
      have hz := LocalRep.none_inv (by simpa only [hc] using h slot)
      rw [hz.1, take_empty] at hs
      cases hs
    | some cell =>
      have hr := LocalRep.some_inv (by simpa only [hc] using h slot)
      obtain ⟨moved, a, b, hm, hv, hf, ha, hperm⟩ := hr.take path hs
      exact ⟨cell, moved, a, b, rfl, hm, hv, hf, h.remask hc ha, hperm⟩

def destroyLocal (memory : Memory) (cell : Option Cell) (part : Slot) : Option (List Nat × DropWork) :=
  match cell with
  | some cell => destroy memory cell part
  | none => match part with
    | .empty => some ([], {})
    | _ => none

theorem LocalRep.destroy {memory : Memory} {cell : Option Cell} {part : Slot} {owners : List Nat}
    (h : LocalRep memory cell part owners) : destroyLocal memory cell part = some (owners, part.dropWork) := by
  cases h with
  | empty => simp only [destroyLocal, Slot.dropWork]
  | stored hr => simp only [destroyLocal, hr.destroy]

theorem LocalRep.boxes {memory : Memory} {cell : Option Cell} {part : Slot} {owners : List Nat}
    (h : LocalRep memory cell part owners) : owners.length = part.dropWork.boxes := by
  cases h with
  | empty => simp only [List.length_nil, Slot.dropWork]
  | stored hr => exact hr.boxes

theorem EnvRep.of_full {memory : Memory} {raw : LookupSource.Heap.Locals} {state : Env} {owners : OwnerState}
    (h : LookupSource.Heap.EnvRep memory raw state)
    (hf : ∀ slot cell, raw slot = some cell → Footprint memory cell (owners slot))
    (hn : ∀ slot, raw slot = none → owners slot = []) :
    EnvRep memory raw (Partial.Locals.lift state) owners := by
  intro slot
  cases hs : state slot with
  | none =>
    cases hc : raw slot with
    | none =>
      simpa only [Partial.Locals.lift, hs, hc, hn slot hc] using LocalRep.empty (memory := memory)
    | some cell =>
      have hr : Option.Rel (Represents memory) (some cell) none := by simpa only [hs, hc] using h slot
      cases hr
  | some value =>
    obtain ⟨cell, hc, hv⟩ := h.get hs
    simpa only [Partial.Locals.lift, hs, hc] using LocalRep.stored (Rep.of_full hv (hf slot cell hc))

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
