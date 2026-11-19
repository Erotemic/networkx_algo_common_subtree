module

public import SubtreeProofs.Rust.SourceFrameInventory

/-! Bounded activations and suspended caller inventories. Scans derive their
resources from current roots/masks and validate live stack classes. Caller data,
ownership and shared-loan footprints transport together across retained worlds. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

structure Activation where
  frame : Nat
  count : Nat
  roots : Roots
  state : Partial.Locals

def Activation.Valid (a : Activation) (world : World) : Prop :=
  Bounded a.roots a.count ∧ ∃ guards, Frame world a.frame a.roots a.state guards

structure Scanned (world : World) (a : Activation) (r : Resources) : Prop where
  bounded : Bounded a.roots a.count
  inventory : Inventory world a.frame a.roots a.state (List.range a.count) r
  frame : Frame world a.frame a.roots a.state r.reads

theorem Scanned.valid {world : World} {a : Activation} {r : Resources} (h : Scanned world a r) : a.Valid world :=
  ⟨h.bounded, r.reads, h.frame⟩

def Activation.scan (a : Activation) (world : World) : Option Resources :=
  inspect world a.frame a.roots a.state (List.range a.count)

def Activation.scanExcept (a : Activation) (world : World) (destination : Nat) : Option Resources :=
  inspect world a.frame a.roots a.state (remainingSlots a.count destination)

theorem Activation.scan_complete {world : World} (a : Activation) (h : a.Valid world) :
    ∃ r, a.scan world = some r ∧ Scanned world a r := by
  obtain ⟨bound, guards, hf⟩ := h
  obtain ⟨r, hr, hi⟩ := hf.inspect (List.range a.count)
  refine ⟨r, hr, bound, hi, hi.frame hf ?_⟩
  intro slot binding hs
  apply List.mem_range.mpr
  by_contra hn
  have he := bound slot (by omega)
  rw [hs] at he
  cases he

theorem Activation.scan_spec {world : World} {a : Activation} (h : a.Valid world) {r : Resources}
    (hr : a.scan world = some r) : Scanned world a r := by
  obtain ⟨actual, hs, hv⟩ := a.scan_complete h
  have he := Option.some.inj (hs.symm.trans hr)
  cases he
  exact hv

theorem Activation.context_complete {world : World} (a : Activation) (h : a.Valid world) (destination : Nat) :
    ∃ r, a.scanExcept world destination = some r ∧
      Inventory world a.frame a.roots a.state (remainingSlots a.count destination) r ∧
      Frame world a.frame (a.roots.set destination none) (a.state.set destination .empty) r.reads := by
  obtain ⟨bound, guards, hf⟩ := h
  obtain ⟨r, hr, hi⟩ := hf.inspect (remainingSlots a.count destination)
  exact ⟨r, hr, hi, hi.context hf bound⟩

theorem Activation.context_spec {world : World} {a : Activation} (h : a.Valid world) (destination : Nat) {r : Resources}
    (hr : a.scanExcept world destination = some r) :
    Frame world a.frame (a.roots.set destination none) (a.state.set destination .empty) r.reads := by
  obtain ⟨actual, hs, _, hf⟩ := a.context_complete h destination
  have he := Option.some.inj (hs.symm.trans hr)
  cases he
  exact hf

theorem Scanned.transport {before after : World} {a : Activation} {r : Resources}
    (h : Scanned before a r) (hp : Preserves before after r.reads) : Scanned after a r :=
  ⟨h.bounded, h.inventory.transport hp, h.frame.preserve hp⟩

theorem Scanned.loan_coverage {world : World} {a : Activation} {r : Resources} (h : Scanned world a r)
    (slot : Nat) {binding : Binding} (hr : a.roots slot = some binding) :
    ∃ cell loans, world.memory[binding.address]? = some cell ∧ BorrowFootprint world.memory cell (a.state slot) loans ∧ loans ⊆ r.loans := by
  apply h.inventory.loan_coverage ?_ hr
  apply List.mem_range.mpr
  by_contra hn
  have hh := h.bounded slot (by omega)
  rw [hr] at hh
  cases hh

inductive Callers (world : World) : List Activation → Resources → Prop where
  | nil : Callers world [] {}
  | cons {a : Activation} {stack : List Activation} {first rest : Resources} :
      Scanned world a first → Callers world stack rest → Callers world (a :: stack) (first.plus rest)

def scanCallers (world : World) : List Activation → Option Resources
  | [] => some {}
  | a :: stack => do
    let first ← a.scan world
    let rest ← scanCallers world stack
    some (first.plus rest)

theorem scanCallers_complete {world : World} (stack : List Activation) (h : ∀ a ∈ stack, a.Valid world) :
    ∃ r, scanCallers world stack = some r ∧ Callers world stack r := by
  induction stack with
  | nil => exact ⟨{}, rfl, .nil⟩
  | cons a stack ih =>
    obtain ⟨first, hf, hv⟩ := a.scan_complete (h a (by simp))
    obtain ⟨rest, hr, hv'⟩ := ih (fun a ha => h a (by simp [ha]))
    exact ⟨first.plus rest, by simp only [scanCallers, hf, hr, Bind.bind, Option.bind], .cons hv hv'⟩

theorem scanCallers_spec {world : World} {stack : List Activation} (h : ∀ a ∈ stack, a.Valid world) {r : Resources}
    (hr : scanCallers world stack = some r) : Callers world stack r := by
  obtain ⟨actual, hs, hv⟩ := scanCallers_complete stack h
  have he := Option.some.inj (hs.symm.trans hr)
  cases he
  exact hv

theorem Callers.alive {world : World} {stack : List Activation} {r : Resources} (h : Callers world stack r) :
    AliveOn world.live r.reads := by
  induction h with
  | nil => simp [AliveOn]
  | cons first rest ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact first.frame.alive a ha
    · exact ih a ha

theorem Callers.get {world : World} {stack : List Activation} {r : Resources} (h : Callers world stack r)
    {a : Activation} (ha : a ∈ stack) :
    ∃ current, Scanned world a current ∧ current.reads ⊆ r.reads ∧ current.owners ⊆ r.owners ∧ current.loans ⊆ r.loans := by
  induction h with
  | nil => cases ha
  | @cons first stack head tail hs rest ih =>
    rcases List.mem_cons.mp ha with he | ha
    · subst first
      exact ⟨head, hs, fun _ hx => List.mem_append_left _ hx,
        fun _ hx => List.mem_append_left _ hx, fun _ hx => List.mem_append_left _ hx⟩
    · obtain ⟨current, hv, hr, ho, hl⟩ := ih ha
      exact ⟨current, hv, fun _ hx => List.mem_append_right _ (hr hx),
        fun _ hx => List.mem_append_right _ (ho hx), fun _ hx => List.mem_append_right _ (hl hx)⟩

theorem Callers.transport {before after : World} {stack : List Activation} {r : Resources}
    (h : Callers before stack r) (hp : Preserves before after r.reads) : Callers after stack r := by
  induction h with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (first.transport (hp.weaken (fun _ ha => List.mem_append_left _ ha)))
      (ih (hp.weaken (fun _ ha => List.mem_append_right _ ha)))

theorem Callers.loans_subset_reads {world : World} {stack : List Activation} {r : Resources}
    (h : Callers world stack r) : r.loans ⊆ r.reads := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (first.inventory.loans_subset_reads ha)
    · exact List.mem_append_right _ (ih ha)

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
