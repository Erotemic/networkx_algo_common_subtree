module

public import SubtreeProofs.Rust.SourceOwnerPackets
public import SubtreeProofs.Rust.SourceActivationLoanViews

/-! Exact owner identities survive certified reference-view endings and
retained-world transport. Removing one local here constructs a mathematical
store context; actual executions must account for its extracted owners. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

theorem ownerList_empty (memory : Memory) (raw : Option Cell) : ownerList memory raw .empty = [] := by
  cases raw <;> simp [ownerList, destroyLocal, destroy]

theorem ownerList_shared (memory : Memory) (raw : Option Cell) (value : Value) : ownerList memory raw (.shared value) = [] := by
  cases raw with
  | none => rfl
  | some cell => cases cell <;> simp [ownerList, destroyLocal, destroy]

theorem ownerState_forget (memory : Memory) (raw : Heap.Locals) (code : SourceEval.Code) (slots : List Nat) (state : Partial.Locals) :
    ownerState memory raw (SourceEval.LoanEnding.forget code slots state) = ownerState memory raw state := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    simp only [SourceEval.LoanEnding.forget_cons]
    cases hs : state slot <;> try exact ih state
    dsimp only
    rw [ih]
    split
    next =>
      funext index
      by_cases he : index = slot
      · subst index
        simp only [ownerState, Partial.Locals.set, ite_true, hs, ownerList_empty, ownerList_shared]
      · simp only [ownerState, Partial.Locals.set, he, ite_false]
    next => rfl

theorem OwnerState.collect_set_empty (owners : OwnerState) (slots : List Nat) (slot : Nat) :
    (owners.set slot []).collect slots = owners.collect (slots.filter (· != slot)) := by
  induction slots with
  | nil => rfl
  | cons first rest ih =>
    by_cases he : first = slot
    · subst first
      simpa only [collect, List.flatMap_cons, OwnerState.set, ite_true, List.nil_append,
        List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using ih
    · change (owners.set slot []) first ++ (owners.set slot []).collect rest = _
      rw [ih]
      simp [OwnerState.set, he, collect]

namespace Storage

def Activation.withoutLocal (active : Activation) (slot : Nat) : Activation :=
  { active with roots := active.roots.set slot none, state := active.state.set slot .empty }

theorem Activation.withoutLocal_ownerState (active : Activation) (world : World) (slot : Nat) :
    ownerState world.memory (rawAt world (active.withoutLocal slot).roots) (active.withoutLocal slot).state =
      (ownerState world.memory (rawAt world active.roots) active.state).set slot [] := by
  funext index
  by_cases he : index = slot
  · subst index
    simp only [ownerState, withoutLocal, Partial.Locals.set, OwnerState.set, ite_true, ownerList_empty]
  · simp only [ownerState, withoutLocal, rawAt, Partial.Locals.set, OwnerState.set, Roots.set, he, ite_false]

theorem Activation.withoutLocal_owners (active : Activation) (world : World) (slot : Nat) :
    (active.withoutLocal slot).owners world =
      (ownerState world.memory (rawAt world active.roots) active.state).collect (remainingSlots active.count slot) := by
  change (ownerState world.memory (rawAt world (active.withoutLocal slot).roots) (active.withoutLocal slot).state).collect
    (List.range active.count) = _
  rw [withoutLocal_ownerState, OwnerState.collect_set_empty]
  rfl

theorem Activation.withoutLocal_empty_owners (active : Activation) (world : World) (slot : Nat)
    (h : active.state slot = .empty) : (active.withoutLocal slot).owners world = active.owners world := by
  change (ownerState world.memory (rawAt world (active.withoutLocal slot).roots) (active.withoutLocal slot).state).collect
    (List.range active.count) = _
  rw [withoutLocal_ownerState]
  apply congrArg (fun owners : OwnerState => owners.collect (List.range active.count))
  funext index
  by_cases he : index = slot
  · subst index
    simp only [OwnerState.set, ite_true, ownerState, h, ownerList_empty]
  · simp only [OwnerState.set, he, ite_false]

theorem Activation.withoutLocal_set (active : Activation) (slot : Nat) (part : Slot) :
    ({ active with state := active.state.set slot part } : Activation).withoutLocal slot = active.withoutLocal slot := by
  simp only [withoutLocal, locals_set_overwrite]

theorem Activation.owners_partition (active : Activation) (world : World) (slot : Nat) (hs : slot < active.count)
    {owners : List Nat} (h : ownerState world.memory (rawAt world active.roots) active.state slot = owners) :
    (active.owners world).Perm (owners ++ (active.withoutLocal slot).owners world) := by
  have hp := OwnerState.collect_partition (ownerState world.memory (rawAt world active.roots) active.state)
    (List.range active.count) List.nodup_range slot (List.mem_range.mpr hs) owners [] (by rw [h]; simp)
  change (active.owners world).Perm (owners ++
    (ownerState world.memory (rawAt world (active.withoutLocal slot).roots) (active.withoutLocal slot).state).collect (List.range active.count))
  rw [withoutLocal_ownerState]
  exact hp

theorem Activation.forgetRefs_owners (active : Activation) (world : World) (code : SourceEval.Code) :
    (active.forgetRefs code).owners world = active.owners world := by
  change (ownerState world.memory (rawAt world active.roots) (SourceEval.LoanEnding.forget code (List.range active.count) active.state)).collect
    (List.range active.count) = _
  rw [ownerState_forget]
  rfl

theorem Frame.ownerState_preserve {before after : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame before frame roots state guards) (hp : Preserves before after guards) :
    Addressed.ownerState after.memory (rawAt after roots) state = Addressed.ownerState before.memory (rawAt before roots) state := by
  funext slot
  cases hr : roots slot with
  | none =>
    have he : state slot = .empty := by simpa only [hr] using h.slots slot
    simp only [Addressed.ownerState, rawAt, hr, he, Bind.bind, Option.bind, ownerList_empty]
  | some binding =>
    obtain ⟨cell, used, hc, _, hg, hu⟩ := h.get hr
    obtain ⟨r, _, he, hv⟩ := hg.resources
    have hroot := hp.reads binding.address (hu (List.mem_append_right _ (by simp))) cell hc
    have retained : Retains before.memory after.memory r.reads := hp.reads.weaken (fun a ha =>
      hu (List.mem_append_left _ (he ▸ ha)))
    have hpost := hv.transport retained
    have hold : ownerList before.memory (some cell) (state slot) = r.owners := (LocalRep.stored hv.owned).ownerList
    have hnew : ownerList after.memory (some cell) (state slot) = r.owners := (LocalRep.stored hpost.owned).ownerList
    simpa only [Addressed.ownerState, rawAt, hr, hc, hroot, Bind.bind, Option.bind] using hnew.trans hold.symm

theorem OwnerFrame.write {world : World} {owners : List Nat} (h : OwnerFrame world owners) (address : Nat) (cell : Cell) :
    OwnerFrame (world.write address cell) owners := ⟨h.unique, h.classified, h.alive⟩

end Storage

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
