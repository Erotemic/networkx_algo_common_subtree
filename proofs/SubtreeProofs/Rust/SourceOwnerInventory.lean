module

public import SubtreeProofs.Rust.SourceActivationInventory
public import SubtreeProofs.Rust.SourcePartialHeapLocals

/-! Canonical complete owner occurrences for actual partial local storage.
The canonical lists are justified by representation, never by treating failed
traversal as an empty valid resource. Finite collection connects these lists to
actual activation inventories and supports exact move partitions. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

def ownerList (memory : Memory) (raw : Option Cell) (part : Slot) : List Nat :=
  ((destroyLocal memory raw part).map Prod.fst).getD []

def ownerState (memory : Memory) (raw : Heap.Locals) (state : Partial.Locals) : OwnerState :=
  fun slot => ownerList memory (raw slot) (state slot)

def OwnerState.collect (owners : OwnerState) (slots : List Nat) : List Nat := slots.flatMap owners

theorem LocalRep.ownerList {memory : Memory} {raw : Option Cell} {part : Slot} {owners : List Nat}
    (h : LocalRep memory raw part owners) : ownerList memory raw part = owners := by
  simp only [Addressed.ownerList, h.destroy, Option.map_some, Option.getD_some]

theorem EnvRep.ownerState {memory : Memory} {raw : Heap.Locals} {state : Partial.Locals} {owners : OwnerState}
    (h : EnvRep memory raw state owners) : ownerState memory raw state = owners := by
  funext slot
  exact (h slot).ownerList

theorem OwnerState.collect_set_absent (owners : OwnerState) (slot : Nat) (replacement : List Nat) (slots : List Nat)
    (hs : slot ∉ slots) : (owners.set slot replacement).collect slots = owners.collect slots := by
  induction slots with
  | nil => rfl
  | cons first rest ih =>
    have he : first ≠ slot := fun h => hs (List.mem_cons.mpr (Or.inl h.symm))
    have ht : slot ∉ rest := fun h => hs (List.mem_cons_of_mem _ h)
    change (owners.set slot replacement) first ++ (owners.set slot replacement).collect rest =
      owners first ++ owners.collect rest
    rw [ih ht]
    simp only [OwnerState.set, he, ite_false]

theorem OwnerState.collect_partition (owners : OwnerState) (slots : List Nat) (hn : slots.Nodup)
    (slot : Nat) (hs : slot ∈ slots) (moved remaining : List Nat)
    (hp : (owners slot).Perm (moved ++ remaining)) :
    (owners.collect slots).Perm (moved ++ (owners.set slot remaining).collect slots) := by
  induction slots with
  | nil => cases hs
  | cons first rest ih =>
    have hnodup := List.nodup_cons.mp hn
    by_cases he : first = slot
    · subst first
      change (owners slot ++ owners.collect rest).Perm
        (moved ++ ((owners.set slot remaining) slot ++ (owners.set slot remaining).collect rest))
      have tail := collect_set_absent owners slot remaining rest hnodup.1
      rw [tail]
      simpa only [OwnerState.set, ite_true, List.append_assoc] using
        hp.append_right (owners.collect rest)
    · have hmem : slot ∈ rest := (List.mem_cons.mp hs).resolve_left (Ne.symm he)
      have old := (ih hnodup.2 hmem).append_left (owners first)
      have swap : (owners first ++ (moved ++ (owners.set slot remaining).collect rest)).Perm
          (moved ++ (owners first ++ (owners.set slot remaining).collect rest)) :=
        List.perm_append_comm_assoc _ _ _
      simpa only [collect, List.flatMap_cons, OwnerState.set, he, ite_false] using old.trans swap

namespace Storage

def Activation.owners (active : Activation) (world : World) : List Nat :=
  (ownerState world.memory (rawAt world active.roots) active.state).collect (List.range active.count)

theorem Frame.ownerState {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) :
    Addressed.EnvRep world.memory (rawAt world roots) state (Addressed.ownerState world.memory (rawAt world roots) state) := by
  intro slot
  obtain ⟨r, _, hr⟩ := h.inspectSlot slot
  simpa only [Addressed.ownerState, hr.source.ownerList] using hr.source

theorem Inventory.owners {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat} {r : Resources}
    (h : Inventory world frame roots state slots r) :
    (Addressed.ownerState world.memory (rawAt world roots) state).collect slots = r.owners := by
  induction h with
  | nil => rfl
  | cons first rest ih =>
    simp only [OwnerState.collect, List.flatMap_cons, Addressed.ownerState, first.source.ownerList, Resources.plus]
    exact congrArg (fun tail => _ ++ tail) ih

theorem Activation.scan_owners {world : World} {active : Activation} (h : active.Valid world) {r : Resources}
    (hs : active.scan world = some r) : active.owners world = r.owners :=
  (Activation.scan_spec h hs).inventory.owners

theorem Activation.move_root_lt {world : World} {active : Activation} (h : active.Valid world)
    {place : Place} {value : Value} {after : Partial.Locals}
    (hm : active.state.move place = some (value, after)) : (splitPlace place).1 < active.count := by
  obtain ⟨bound, guards, hf⟩ := h
  obtain ⟨root, _, _, _, hr, _, _, _, _, _⟩ := hf.ownerState.move hm
  by_contra hn
  have he := bound (splitPlace place).1 (by omega)
  simp only [rawAt, he, Bind.bind, Option.bind] at hr
  cases hr

end Storage

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
