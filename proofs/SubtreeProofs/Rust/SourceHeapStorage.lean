module

public import SubtreeProofs.Rust.SourceHeapPlaces

/-! Allocation classes, live storage roots and retained caller frames over the
existing heap. Stack roots are symbolic storage identities, not Box owners.
Stored data is immutable; ending storage changes liveness. Reassignment and
initialization-mask changes require separate preservation/conflict arguments. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open LookupSource.Heap

inductive Class where
  | box
  | stack (frame slot generation : Nat)
  deriving DecidableEq, Repr

structure World where
  memory : Memory
  classes : Nat → Option Class
  live : Live

def World.WellFormed (world : World) : Prop :=
  (∀ address, (world.classes address).isSome = true ↔ address < world.memory.length) ∧
  ∀ address, world.live address = true → address < world.memory.length

def World.allocate (world : World) (kind : Class) (cell : Cell) : World :=
  ⟨world.memory ++ [cell],
    fun address => if address = world.memory.length then some kind else world.classes address,
    fun address => if address = world.memory.length then true else world.live address⟩

def World.retire (world : World) (discarded : List Nat) : World :=
  { world with live := Addressed.retire world.live discarded }

theorem World.allocate_spec (world : World) (kind : Class) (cell : Cell) :
    Extends world.memory (world.allocate kind cell).memory ∧
      (world.allocate kind cell).memory[world.memory.length]? = some cell ∧
      (world.allocate kind cell).classes world.memory.length = some kind ∧
      (world.allocate kind cell).live world.memory.length = true ∧
      (world.allocate kind cell).memory.length = world.memory.length + 1 := by
  exact ⟨Extends.append _ _, (alloc_fresh _ _).2.1, by simp [allocate], by simp [allocate], by simp [allocate]⟩

theorem World.WellFormed.allocate {world : World} (h : world.WellFormed) (kind : Class) (cell : Cell) :
    (world.allocate kind cell).WellFormed := by
  constructor
  · intro address
    by_cases ha : address = world.memory.length
    · simp [World.allocate, ha]
    · simpa only [World.allocate, ha, ite_false, List.length_append, List.length_singleton,
        show address < world.memory.length + 1 ↔ address < world.memory.length by omega] using h.1 address
  · intro address hl
    by_cases ha : address = world.memory.length
    · simp [World.allocate, ha]
    · have hb : world.live address = true := by simpa only [World.allocate, ha, ite_false] using hl
      have hc := h.2 address hb
      simp only [World.allocate, List.length_append, List.length_singleton]
      omega

theorem World.WellFormed.retire {world : World} (h : world.WellFormed) (discarded : List Nat) :
    (world.retire discarded).WellFormed := by
  refine ⟨h.1, ?_⟩
  intro address hl
  by_cases ha : address ∈ discarded
  · simp [World.retire, retire_member world.live ha] at hl
  · exact h.2 address (by simpa only [World.retire, retire_other world.live ha] using hl)

/-- A transition preserves the stored graph, allocation class and liveness
on the explicitly retained read resources. No ownership transfer is assumed. -/
structure Keeps (before after : World) (guards : List Nat) : Prop where
  memory : Extends before.memory after.memory
  classes : ∀ address kind, before.classes address = some kind → after.classes address = some kind
  alive : ∀ address ∈ guards, before.live address = true → after.live address = true

theorem Keeps.refl (world : World) (guards : List Nat) : Keeps world world guards :=
  ⟨Extends.refl _, fun _ _ h => h, fun _ _ h => h⟩

theorem Keeps.trans {first second third : World} {guards : List Nat}
    (h₁ : Keeps first second guards) (h₂ : Keeps second third guards) : Keeps first third guards :=
  ⟨h₁.memory.trans h₂.memory, fun a k h => h₂.classes a k (h₁.classes a k h),
    fun a ha h => h₂.alive a ha (h₁.alive a ha h)⟩

theorem Keeps.weaken {before after : World} {guards smaller : List Nat} (h : Keeps before after guards)
    (hs : smaller ⊆ guards) : Keeps before after smaller :=
  ⟨h.memory, h.classes, fun a ha => h.alive a (hs ha)⟩

theorem World.allocate_keeps {world : World} (hw : world.WellFormed) (kind : Class) (cell : Cell)
    (guards : List Nat) : Keeps world (world.allocate kind cell) guards := by
  refine ⟨(world.allocate_spec kind cell).1, ?_, ?_⟩
  · intro address prior hc
    have hb : address < world.memory.length := (hw.1 address).mp (by simp [hc])
    have hn : address ≠ world.memory.length := by omega
    simpa only [allocate, hn, ite_false] using hc
  · intro address _ hl
    by_cases ha : address = world.memory.length <;> simp [allocate, ha, hl]

theorem World.retire_keeps (world : World) {guards discarded : List Nat}
    (hs : ∀ address ∈ guards, address ∉ discarded) : Keeps world (world.retire discarded) guards :=
  ⟨Extends.refl _, fun _ _ h => h, fun a ha hl => by
    simpa only [World.retire, retire_other world.live (hs a ha)] using hl⟩

def BoxOwners (world : World) (owners : List Nat) : Prop :=
  ∀ address ∈ owners, world.classes address = some .box

theorem BoxOwners.allocate {world : World} (hw : world.WellFormed) {owners : List Nat}
    (h : BoxOwners world owners) (cell : Cell) :
    BoxOwners (world.allocate .box cell) (owners ++ [world.memory.length]) := by
  intro address ha
  rcases List.mem_append.mp ha with ha | ha
  · exact (world.allocate_keeps hw .box cell []).classes address .box (h address ha)
  · simpa only [List.mem_singleton.mp ha] using (world.allocate_spec .box cell).2.2.1

theorem BoxOwners.stack_disjoint {world : World} {owners : List Nat} (h : BoxOwners world owners)
    {address frame slot generation : Nat} (hs : world.classes address = some (.stack frame slot generation)) :
    address ∉ owners := by
  intro ha
  have hh := (h address ha).symm.trans hs
  cases hh

theorem BoxOwners.retire_stack {world : World} {owners : List Nat} (h : BoxOwners world owners)
    {address frame slot generation : Nat} (hs : world.classes address = some (.stack frame slot generation)) :
    (world.retire owners).live address = world.live address :=
  retire_other _ (h.stack_disjoint hs)

/-- A retained finite read graph and its allocation liveness. Initialization
at creation comes from `Frame.borrow`; legal mutation/moves while a loan is
retained require conflict checking, not merely this stored-data proposition. -/
structure Loan (world : World) (pointer : Pointer) (value : Value) (guards : List Nat) : Prop where
  valid : ∃ cell, read world.memory pointer = some cell ∧ Graph world.memory cell value guards
  alive : AliveOn world.live (guards ++ [pointer.root])

theorem Loan.readLive {world : World} {pointer : Pointer} {value : Value} {guards : List Nat}
    (h : Loan world pointer value guards) :
    ∃ cell, readLive world.memory world.live pointer = some cell ∧ Readable world.memory world.live cell value := by
  obtain ⟨cell, hr, hg⟩ := h.valid
  have hl : world.live pointer.root = true := h.alive _ (List.mem_append_right _ (by simp))
  exact ⟨cell, by simp only [Addressed.readLive, hl, ↓reduceIte, hr], guards, hg,
    fun a ha => h.alive a (List.mem_append_left _ ha)⟩

theorem Loan.shared {world : World} {pointer : Pointer} {value : Value} {guards : List Nat}
    (h : Loan world pointer value guards) : Readable world.memory world.live (.shared pointer) (.reference value) := by
  obtain ⟨cell, hr, hg⟩ := h.valid
  exact ⟨guards ++ [pointer.root], .shared hr hg, h.alive⟩

theorem Loan.keep {before after : World} {pointer : Pointer} {value : Value} {guards : List Nat}
    (h : Loan before pointer value guards) (hk : Keeps before after (guards ++ [pointer.root])) :
    Loan after pointer value guards := by
  obtain ⟨cell, hr, hg⟩ := h.valid
  exact ⟨⟨cell, read_extends hk.memory hr, hg.mono hk.memory⟩, fun a ha => hk.alive a ha (h.alive a ha)⟩

theorem Loan.retire {world : World} {pointer : Pointer} {value : Value} {guards discarded : List Nat}
    (h : Loan world pointer value guards) (hs : ∀ address ∈ guards ++ [pointer.root], address ∉ discarded) :
    Loan (world.retire discarded) pointer value guards := h.keep (world.retire_keeps hs)

theorem Loan.root_not_retired {world : World} {pointer : Pointer} {value : Value} {guards discarded : List Nat}
    (h : Loan (world.retire discarded) pointer value guards) : pointer.root ∉ discarded := by
  intro ha
  have hl := h.alive pointer.root (List.mem_append_right _ (by simp))
  simp only [World.retire, retire_member world.live ha] at hl
  cases hl

theorem Loan.retire_iff {world : World} {pointer : Pointer} {value : Value} {guards discarded : List Nat}
    (h : Loan world pointer value guards) :
    Loan (world.retire discarded) pointer value guards ↔
      ∀ address ∈ guards ++ [pointer.root], address ∉ discarded := by
  constructor
  · intro after address ha hd
    have hl := after.alive address ha
    simp only [World.retire, retire_member world.live hd] at hl
    cases hl
  · exact h.retire

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
