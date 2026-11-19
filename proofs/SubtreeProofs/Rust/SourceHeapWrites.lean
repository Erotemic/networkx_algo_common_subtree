module

public import SubtreeProofs.Rust.SourceHeapTransport
public import SubtreeProofs.Rust.SourceEvalLocalBorrow

/-! Guarded in-place stack writes preserve retained reference graphs and
caller frames. Allocation identity, class, liveness and memory length stay
fixed. Mutation authorization checks the full transitive read guard. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open LookupSource.Heap

structure Preserves (before after : World) (guards : List Nat) : Prop where
  reads : Retains before.memory after.memory guards
  classes : ∀ address kind, before.classes address = some kind → after.classes address = some kind
  alive : ∀ address ∈ guards, before.live address = true → after.live address = true

theorem Preserves.refl (world : World) (guards : List Nat) : Preserves world world guards :=
  ⟨Retains.refl _ _, fun _ _ h => h, fun _ _ h => h⟩

theorem Preserves.trans {first second third : World} {guards : List Nat}
    (h₁ : Preserves first second guards) (h₂ : Preserves second third guards) : Preserves first third guards :=
  ⟨h₁.reads.trans h₂.reads, fun a k h => h₂.classes a k (h₁.classes a k h),
    fun a ha h => h₂.alive a ha (h₁.alive a ha h)⟩

theorem Preserves.weaken {before after : World} {guards smaller : List Nat} (h : Preserves before after guards)
    (hs : smaller ⊆ guards) : Preserves before after smaller :=
  ⟨h.reads.weaken hs, h.classes, fun a ha => h.alive a (hs ha)⟩

theorem Keeps.preserves {before after : World} {guards : List Nat} (h : Keeps before after guards) :
    Preserves before after guards := ⟨Retains.of_extends h.memory _, h.classes, h.alive⟩

theorem Loan.preserve {before after : World} {pointer : Pointer} {value : Value} {guards : List Nat}
    (h : Loan before pointer value guards) (hp : Preserves before after (guards ++ [pointer.root])) :
    Loan after pointer value guards := by
  obtain ⟨cell, hr, hg⟩ := h.valid
  exact ⟨⟨cell, hp.reads.read (List.mem_append_right _ (by simp)) hr,
    hg.transport (hp.reads.weaken (fun _ ha => List.mem_append_left _ ha))⟩,
    fun a ha => hp.alive a ha (h.alive a ha)⟩

theorem Frame.preserve {before after : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame before frame roots state guards) (hp : Preserves before after guards) :
    Frame after frame roots state guards := by
  refine ⟨fun a ha => hp.alive a ha (h.alive a ha), ?_⟩
  intro slot
  cases hr : roots slot with
  | none => simpa only [hr] using h.slots slot
  | some binding =>
    obtain ⟨cell, used, hc, ht, hg, hs⟩ := h.get hr
    have ha : binding.address ∈ guards := hs (List.mem_append_right _ (by simp))
    exact ⟨cell, used, hp.reads _ ha _ hc, hp.classes _ _ ht,
      hg.transport (hp.reads.weaken (fun _ ha => hs (List.mem_append_left _ ha))), hs⟩

def World.write (world : World) (address : Nat) (cell : Cell) : World :=
  { world with memory := world.memory.set address cell }

theorem World.write_spec (world : World) {address : Nat} (hb : address < world.memory.length) (cell : Cell) :
    (world.write address cell).memory[address]? = some cell ∧
      (world.write address cell).memory.length = world.memory.length ∧
      (world.write address cell).classes = world.classes ∧ (world.write address cell).live = world.live :=
  ⟨List.getElem?_set_self hb, List.length_set, rfl, rfl⟩

theorem World.WellFormed.write {world : World} (h : world.WellFormed) (address : Nat) (cell : Cell) :
    (world.write address cell).WellFormed := by
  simpa only [World.WellFormed, World.write, List.length_set] using h

theorem World.write_preserves (world : World) {address : Nat} {guards : List Nat} (hs : address ∉ guards) (cell : Cell) :
    Preserves world (world.write address cell) guards := by
  refine ⟨?_, fun _ _ h => h, fun _ _ h => h⟩
  intro other ho value hr
  have hn : address ≠ other := fun he => hs (he.symm ▸ ho)
  simpa only [World.write, List.getElem?_set_ne hn] using hr

def World.writeStack (world : World) (frame slot : Nat) (binding : Binding) (guards : List Nat) (cell : Cell) : Option World :=
  if world.classes binding.address = some (.stack frame slot binding.generation) ∧
      world.live binding.address = true ∧ binding.address < world.memory.length ∧ binding.address ∉ guards then
    some (world.write binding.address cell)
  else none

theorem World.writeStack_iff {world after : World} {frame slot : Nat} {binding : Binding} {guards : List Nat} {cell : Cell} :
    world.writeStack frame slot binding guards cell = some after ↔
      world.classes binding.address = some (.stack frame slot binding.generation) ∧
      world.live binding.address = true ∧ binding.address < world.memory.length ∧ binding.address ∉ guards ∧
      after = world.write binding.address cell := by
  unfold writeStack
  split
  next h =>
    constructor
    · intro he
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, (Option.some.inj he).symm⟩
    · rintro ⟨_, _, _, _, rfl⟩
      rfl
  next h =>
    constructor
    · intro he; cases he
    · rintro ⟨hc, hl, hb, hs, _⟩
      exact False.elim (h ⟨hc, hl, hb, hs⟩)

theorem World.writeStack_success {world : World} {frame slot : Nat} {binding : Binding} {guards : List Nat}
    (hw : world.WellFormed) (hc : world.classes binding.address = some (.stack frame slot binding.generation))
    (hl : world.live binding.address = true) (hs : binding.address ∉ guards) (cell : Cell) :
    world.writeStack frame slot binding guards cell = some (world.write binding.address cell) := by
  exact World.writeStack_iff.mpr ⟨hc, hl, (hw.1 _).mp (by simp [hc]), hs, rfl⟩

theorem Loan.write {world : World} {pointer : Pointer} {value : Value} {guards : List Nat}
    (h : Loan world pointer value guards) {address : Nat} (hs : address ∉ guards ++ [pointer.root]) (cell : Cell) :
    Loan (world.write address cell) pointer value guards := h.preserve (world.write_preserves hs cell)

theorem Frame.write {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) {address : Nat} (hs : address ∉ guards) (cell : Cell) :
    Frame (world.write address cell) frame roots state guards := h.preserve (world.write_preserves hs cell)

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
