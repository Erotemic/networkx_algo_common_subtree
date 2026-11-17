module

public import SubtreeProofs.Rust.SourceHeapResources
public import SubtreeProofs.Rust.SourceEvalAddressedAssignments

/-! Finite inspection derives actual read/owner/loan inventories from local
roots and partial masks. Context extraction covers every remaining live binding;
it does not depend on a caller-supplied postcondition about the desired frame. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open LookupSource.Heap

def rawAt (world : World) (roots : Roots) (slot : Nat) : Option Cell := do
  let binding ← roots slot
  world.memory[binding.address]?

inductive LocalResources (world : World) (frame : Nat) (roots : Roots) (state : Partial.Locals) : Nat → Resources → Prop where
  | vacant {slot : Nat} : roots slot = none → state slot = .empty → LocalResources world frame roots state slot {}
  | stored {slot : Nat} {binding : Binding} {cell : Cell} {r : Resources} :
      roots slot = some binding → world.memory[binding.address]? = some cell →
      world.classes binding.address = some (.stack frame slot binding.generation) →
      ResourceRep world.memory cell (state slot) r → AliveOn world.live (r.atRoot binding.address).reads →
      LocalResources world frame roots state slot (r.atRoot binding.address)

theorem LocalResources.alive {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) : AliveOn world.live r.reads := by
  cases h with
  | vacant _ _ => simp [AliveOn]
  | stored _ _ _ _ hl => exact hl

theorem LocalResources.source {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) : LocalRep world.memory (rawAt world roots slot) (state slot) r.owners := by
  cases h with
  | vacant hr he => simpa only [rawAt, hr, Bind.bind, Option.bind, he] using LocalRep.empty (memory := world.memory)
  | stored hr hc _ hv _ => simpa only [rawAt, hr, hc, Bind.bind, Option.bind, Resources.atRoot] using LocalRep.stored hv.owned

theorem LocalResources.boxes {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) : r.owners.length = (state slot).dropWork.boxes := h.source.boxes

theorem LocalResources.anchored {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) {binding : Binding} (hr : roots slot = some binding) :
    Anchored world frame slot binding (state slot) r.reads := by
  cases h with
  | vacant hn _ => rw [hr] at hn; cases hn
  | stored hs hc ht hv _ =>
    have he := Option.some.inj (hr.symm.trans hs)
    cases he
    exact ⟨_, _, hc, ht, hv.graph, List.Subset.refl _⟩

theorem LocalResources.loans_subset_reads {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) : r.loans ⊆ r.reads := by
  cases h with
  | vacant _ _ => simp
  | stored _ _ _ hv _ => exact fun _ ha => List.mem_append_left _ (hv.borrowed.subset_reads hv.graph ha)

theorem LocalResources.borrowed {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) {binding : Binding} (hr : roots slot = some binding) :
    ∃ cell, world.memory[binding.address]? = some cell ∧ BorrowFootprint world.memory cell (state slot) r.loans := by
  cases h with
  | vacant hn _ => rw [hr] at hn; cases hn
  | stored hs hc _ hv _ =>
    have he := Option.some.inj (hr.symm.trans hs)
    cases he
    exact ⟨_, hc, hv.borrowed⟩

def inspectSlot (world : World) (frame : Nat) (roots : Roots) (state : Partial.Locals) (slot : Nat) : Option Resources :=
  match roots slot with
  | none => if SourceEval.Addressed.emptySlot (state slot) then some {} else none
  | some binding =>
    if world.classes binding.address = some (.stack frame slot binding.generation) then do
      let cell ← world.memory[binding.address]?
      let r ← traceResources world.memory cell (state slot)
      let r := r.atRoot binding.address
      if r.reads.all world.live then some r else none
    else none

theorem Frame.inspectSlot {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (slot : Nat) :
    ∃ r, inspectSlot world frame roots state slot = some r ∧ LocalResources world frame roots state slot r := by
  cases hr : roots slot with
  | none =>
    have he : state slot = .empty := by simpa only [hr] using h.slots slot
    exact ⟨{}, by simp only [Storage.inspectSlot, hr, he, SourceEval.Addressed.emptySlot, ↓reduceIte], .vacant hr he⟩
  | some binding =>
    obtain ⟨cell, used, hc, ht, hg, hs⟩ := h.get hr
    obtain ⟨r, he, hreads, hv⟩ := hg.resources
    have hl : AliveOn world.live (r.atRoot binding.address).reads := by
      intro a ha
      exact h.alive a (hs (by simpa only [Resources.atRoot, hreads] using ha))
    have hall : (r.atRoot binding.address).reads.all world.live = true := List.all_eq_true.mpr hl
    exact ⟨r.atRoot binding.address, by simp only [Storage.inspectSlot, hr, ht, hc, he, hall, ↓reduceIte, Bind.bind, Option.bind],
      .stored hr hc ht hv hl⟩

inductive Inventory (world : World) (frame : Nat) (roots : Roots) (state : Partial.Locals) : List Nat → Resources → Prop where
  | nil : Inventory world frame roots state [] {}
  | cons {slot : Nat} {slots : List Nat} {head tail : Resources} :
      LocalResources world frame roots state slot head → Inventory world frame roots state slots tail →
      Inventory world frame roots state (slot :: slots) (head.plus tail)

def inspect (world : World) (frame : Nat) (roots : Roots) (state : Partial.Locals) : List Nat → Option Resources
  | [] => some {}
  | slot :: slots => do
    let first ← inspectSlot world frame roots state slot
    let rest ← inspect world frame roots state slots
    some (first.plus rest)

theorem Frame.inspect {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (slots : List Nat) :
    ∃ r, inspect world frame roots state slots = some r ∧ Inventory world frame roots state slots r := by
  induction slots with
  | nil => exact ⟨{}, rfl, .nil⟩
  | cons slot slots ih =>
    obtain ⟨a, ha, hv⟩ := h.inspectSlot slot
    obtain ⟨b, hb, hv'⟩ := ih
    exact ⟨a.plus b, by simp only [Storage.inspect, ha, hb, Bind.bind, Option.bind], .cons hv hv'⟩

theorem Inventory.alive {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat} {r : Resources}
    (h : Inventory world frame roots state slots r) : AliveOn world.live r.reads := by
  induction h with
  | nil => simp [AliveOn]
  | cons first rest ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact first.alive a ha
    · exact ih a ha

theorem Inventory.get {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat} {r : Resources}
    (h : Inventory world frame roots state slots r) (hs : slot ∈ slots) :
    ∃ item, LocalResources world frame roots state slot item ∧ item.reads ⊆ r.reads ∧
      item.owners ⊆ r.owners ∧ item.loans ⊆ r.loans := by
  induction h with
  | nil => cases hs
  | @cons first slots head tail hv rest ih =>
    rcases List.mem_cons.mp hs with he | hs
    · subst first
      exact ⟨head, hv, fun _ ha => List.mem_append_left _ ha,
        fun _ ha => List.mem_append_left _ ha, fun _ ha => List.mem_append_left _ ha⟩
    · obtain ⟨item, hl, ha, hb, hc⟩ := ih hs
      exact ⟨item, hl, fun _ hx => List.mem_append_right _ (ha hx),
        fun _ hx => List.mem_append_right _ (hb hx), fun _ hx => List.mem_append_right _ (hc hx)⟩

theorem Inventory.boxes {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat} {r : Resources}
    (h : Inventory world frame roots state slots r) : r.owners.length = (slots.map (fun i => (state i).dropWork.boxes)).sum := by
  induction h with
  | nil => rfl
  | cons first rest ih => simp only [Resources.plus, List.length_append, first.boxes, ih, List.map_cons, List.sum_cons]

theorem Inventory.loans_subset_reads {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat} {r : Resources}
    (h : Inventory world frame roots state slots r) : r.loans ⊆ r.reads := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (first.loans_subset_reads ha)
    · exact List.mem_append_right _ (ih ha)

theorem Inventory.loan_coverage {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat} {r : Resources}
    (h : Inventory world frame roots state slots r) (hs : slot ∈ slots) {binding : Binding} (hr : roots slot = some binding) :
    ∃ cell loans, world.memory[binding.address]? = some cell ∧ BorrowFootprint world.memory cell (state slot) loans ∧ loans ⊆ r.loans := by
  obtain ⟨item, hv, _, _, hloans⟩ := h.get hs
  obtain ⟨cell, hc, hb⟩ := hv.borrowed hr
  exact ⟨cell, item.loans, hc, hb, hloans⟩

def Bounded (roots : Roots) (count : Nat) : Prop := ∀ slot, count ≤ slot → roots slot = none

def remainingSlots (count destination : Nat) : List Nat := (List.range count).filter (· != destination)

theorem Inventory.frame {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (base : Frame world frame roots state guards) {slots : List Nat} {r : Resources}
    (h : Inventory world frame roots state slots r)
    (cover : ∀ slot binding, roots slot = some binding → slot ∈ slots) : Frame world frame roots state r.reads := by
  refine ⟨h.alive, ?_⟩
  intro slot
  cases hr : roots slot with
  | none => simpa only [hr] using base.slots slot
  | some binding =>
    obtain ⟨item, hv, hs, _, _⟩ := h.get (cover slot binding hr)
    obtain ⟨cell, used, hc, ht, hg, hu⟩ := hv.anchored hr
    exact ⟨cell, used, hc, ht, hg, fun _ ha => hs (hu ha)⟩

theorem Inventory.context {world : World} {frame count destination : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (base : Frame world frame roots state guards) (bound : Bounded roots count) {r : Resources}
    (h : Inventory world frame roots state (remainingSlots count destination) r) :
    Frame world frame (roots.set destination none) (state.set destination .empty) r.reads := by
  refine ⟨h.alive, ?_⟩
  intro slot
  by_cases hd : slot = destination
  · subst slot; simp only [Roots.set, Partial.Locals.set, ite_true]
  · simp only [Roots.set, Partial.Locals.set, hd, ite_false]
    cases hr : roots slot with
    | none => simpa only [hr] using base.slots slot
    | some binding =>
      have hb : slot < count := by
        by_contra hn
        have hh := bound slot (by omega)
        rw [hr] at hh
        cases hh
      have hs : slot ∈ remainingSlots count destination := by simp [remainingSlots, hb, hd]
      obtain ⟨item, hv, hu, _, _⟩ := h.get hs
      obtain ⟨cell, used, hc, ht, hg, hsub⟩ := hv.anchored hr
      exact ⟨cell, used, hc, ht, hg, fun _ ha => hu (hsub ha)⟩

theorem LocalResources.transport {before after : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources before frame roots state slot r) (hp : Preserves before after r.reads) :
    LocalResources after frame roots state slot r := by
  cases h with
  | vacant hr he => exact .vacant hr he
  | stored hr hc ht hv hl =>
    have hroot := hp.reads _ (List.mem_append_right _ (by simp)) _ hc
    exact .stored hr hroot (hp.classes _ _ ht)
      (hv.transport (hp.reads.weaken (fun _ ha => List.mem_append_left _ ha)))
      (fun a ha => hp.alive a ha (hl a ha))

theorem Inventory.transport {before after : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {slots : List Nat} {r : Resources}
    (h : Inventory before frame roots state slots r) (hp : Preserves before after r.reads) :
    Inventory after frame roots state slots r := by
  induction h with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (first.transport (hp.weaken (fun _ ha => List.mem_append_left _ ha)))
      (ih (hp.weaken (fun _ ha => List.mem_append_right _ ha)))

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
