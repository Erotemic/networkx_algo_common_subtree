module

public import SubtreeProofs.Rust.SourceHeapStorage
public import SubtreeProofs.Rust.SourceEvalHeapMoveDrop

/-! Addressable partial local frames and actual source address expressions.
Retained frames derive guards from their stored graphs, including shared
aliases and stack roots. Full evaluator frame construction/updates, conflict
checking, recursive call traces and region interpretation remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open LookupSource.Heap

structure Binding where
  address : Nat
  generation : Nat
  deriving DecidableEq, Repr

abbrev Roots := Nat → Option Binding

def Roots.set (roots : Roots) (slot : Nat) (binding : Option Binding) : Roots := fun index =>
  if index = slot then binding else roots index

def Anchored (world : World) (frame slot : Nat) (binding : Binding) (part : Slot) (guards : List Nat) : Prop :=
  ∃ cell used, world.memory[binding.address]? = some cell ∧
    world.classes binding.address = some (.stack frame slot binding.generation) ∧
    PartialGraph world.memory cell part used ∧ used ++ [binding.address] ⊆ guards

structure Frame (world : World) (frame : Nat) (roots : Roots) (state : Partial.Locals) (guards : List Nat) : Prop where
  alive : AliveOn world.live guards
  slots : ∀ slot, match roots slot with
    | none => state slot = .empty
    | some binding => Anchored world frame slot binding (state slot) guards

theorem Frame.empty (world : World) (frame : Nat) :
    Frame world frame (fun _ => none) (fun _ => .empty) [] :=
  ⟨by simp [AliveOn], fun _ => rfl⟩

theorem Frame.get {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) {slot : Nat} {binding : Binding} (hr : roots slot = some binding) :
    Anchored world frame slot binding (state slot) guards := by
  simpa only [hr] using h.slots slot

theorem Frame.distinct {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) {first second : Nat} {a b : Binding}
    (h₁ : roots first = some a) (h₂ : roots second = some b) (he : a.address = b.address) : first = second := by
  obtain ⟨_, _, _, hc, _, _⟩ := h.get h₁
  obtain ⟨_, _, _, hd, _, _⟩ := h.get h₂
  rw [he, hd] at hc
  exact (Class.stack.inj (Option.some.inj hc)).2.1.symm

theorem Frame.keep {before after : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame before frame roots state guards) (hk : Keeps before after guards) : Frame after frame roots state guards := by
  refine ⟨fun a ha => hk.alive a ha (h.alive a ha), ?_⟩
  intro slot
  cases hr : roots slot with
  | none => simpa only [hr] using h.slots slot
  | some binding =>
    obtain ⟨cell, used, hc, ht, hg, hs⟩ := h.get hr
    exact ⟨cell, used, hk.memory _ _ hc, hk.classes _ _ ht, hg.mono hk.memory, hs⟩

theorem Frame.weaken {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards larger : List Nat}
    (h : Frame world frame roots state guards) (hs : guards ⊆ larger) (hl : AliveOn world.live larger) :
    Frame world frame roots state larger := by
  refine ⟨hl, ?_⟩
  intro slot
  cases hr : roots slot with
  | none => simpa only [hr] using h.slots slot
  | some binding =>
    obtain ⟨cell, used, hc, ht, hg, hu⟩ := h.get hr
    exact ⟨cell, used, hc, ht, hg, fun _ ha => hs (hu ha)⟩

theorem Frame.retire {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {guards discarded : List Nat} (h : Frame world frame roots state guards)
    (hs : ∀ address ∈ guards, address ∉ discarded) : Frame (world.retire discarded) frame roots state guards :=
  h.keep (world.retire_keeps hs)

theorem Frame.retire_iff {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {guards discarded : List Nat} (h : Frame world frame roots state guards) :
    Frame (world.retire discarded) frame roots state guards ↔ ∀ address ∈ guards, address ∉ discarded := by
  constructor
  · intro after address ha hd
    have hl := after.alive address ha
    simp only [World.retire, retire_member world.live hd] at hl
    cases hl
  · exact h.retire

theorem Frame.allocate {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (hw : world.WellFormed) {slot : Nat} (hn : roots slot = none)
    (generation : Nat) {cell : Cell} {part : Slot} {used : List Nat}
    (hg : PartialGraph world.memory cell part used) (hl : AliveOn world.live used) :
    state slot = .empty ∧ Frame (world.allocate (.stack frame slot generation) cell) frame
      (roots.set slot (some ⟨world.memory.length, generation⟩)) (state.set slot part)
      (guards ++ used ++ [world.memory.length]) := by
  refine ⟨by simpa only [hn] using h.slots slot, ?_⟩
  have hk := world.allocate_keeps hw (.stack frame slot generation) cell (guards ++ used ++ [world.memory.length])
  have hs := world.allocate_spec (.stack frame slot generation) cell
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hk.alive a (List.mem_append_left _ (List.mem_append_left _ ha)) (h.alive a ha)
      · exact hk.alive a (List.mem_append_left _ (List.mem_append_right _ ha)) (hl a ha)
    · simpa only [List.mem_singleton.mp ha] using hs.2.2.2.1
  · intro index
    by_cases hi : index = slot
    · subst index
      simp only [Roots.set, Partial.Locals.set, ite_true]
      exact ⟨cell, used, hs.2.1, hs.2.2.1, hg.mono hs.1, by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (List.mem_append_right _ ha)
        · exact List.mem_append_right _ ha⟩
    · simp only [Roots.set, Partial.Locals.set, hi, ite_false]
      cases hr : roots index with
      | none => simpa only [hr] using h.slots index
      | some binding =>
        obtain ⟨old, oldUsed, hc, ht, hp, hu⟩ := h.get hr
        exact ⟨old, oldUsed, hk.memory _ _ hc, hk.classes _ _ ht, hp.mono hk.memory,
          fun _ ha => List.mem_append_left _ (List.mem_append_left _ (hu ha))⟩

def locate (world : World) (roots : Roots) (place : Place) : Option (Cell × Pointer) := do
  let (slot, path) := splitPlace place
  let binding ← roots slot
  locatePath world.memory (← world.memory[binding.address]?) ⟨binding.address, []⟩ path

def borrow (world : World) (roots : Roots) (place : Place) : Option Cell := do
  let (_, pointer) ← locate world roots place
  if world.live pointer.root then some (.shared pointer) else none

theorem Frame.borrow {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (place : Place) {value : Value} (hr : state.read place = some value) :
    ∃ pointer used, borrow world roots place = some (.shared pointer) ∧ Loan world pointer value used ∧
      used ++ [pointer.root] ⊆ guards := by
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [Partial.Locals.read, hp] at hr
  cases hb : roots slot with
  | none =>
    have he : state slot = .empty := by simpa only [hb] using h.slots slot
    rw [he, Slot.read_empty] at hr
    cases hr
  | some binding =>
    obtain ⟨cell, all, hc, ht, hg, hs⟩ := h.get hb
    have hr' : read world.memory ⟨binding.address, []⟩ = some cell := by
      simp only [Heap.read, hc, bind, Option.bind, Heap.fields]
    obtain ⟨found, pointer, used, hl, hh, hg', hsub⟩ := hg.read ⟨binding.address, []⟩ hr' path hr
    have hused : used ++ [pointer.root] ⊆ guards := fun _ ha => hs (hsub ha)
    have halive : AliveOn world.live (used ++ [pointer.root]) := fun a ha => h.alive a (hused ha)
    have hroot : world.live pointer.root = true := halive _ (List.mem_append_right _ (by simp))
    exact ⟨pointer, used, by simp only [Storage.borrow, Storage.locate, hp, hb, hc, hl, bind, Option.bind, hroot, ↓reduceIte],
      ⟨⟨found, hh, hg'⟩, halive⟩, hused⟩

theorem Loan.typed {world : World} {pointer : Pointer} {value : Value} {guards : List Nat}
    (h : Loan world pointer value guards) {ty : Ty} (ht : SnapshotTyped value ty) :
    ∃ cell, Addressed.readLive world.memory world.live pointer = some cell ∧ Typed world.memory cell ty ∧
      Typed world.memory (.shared pointer) (.shared ty) := by
  obtain ⟨cell, hr, hg⟩ := h.valid
  have hc := hg.represents.typed ht
  have hl := h.alive pointer.root (List.mem_append_right _ (by simp))
  exact ⟨cell, by simp only [Addressed.readLive, hl, ↓reduceIte, hr], hc, .shared hr hc⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.AddressedPrimitives

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem expression_address {world : World} {frame : Nat} {roots : Roots} {state : State} {guards : List Nat}
    (h : Frame world frame roots state guards) (place : Place) {value : Value} (hr : state.read place = some value) :
    expression state (.address place) = some (.reference value, state) ∧
      ∃ pointer used, Storage.borrow world roots place = some (.shared pointer) ∧
        Loan world pointer value used ∧ Readable world.memory world.live (.shared pointer) (.reference value) ∧
        used ++ [pointer.root] ⊆ guards := by
  obtain ⟨pointer, used, hb, hl, hs⟩ := h.borrow place hr
  exact ⟨by simp only [expression, hr, bind, Option.bind], pointer, used, hb, hl, hl.shared, hs⟩

theorem box_new_frame (body : Function → Code) (fuel : Nat) {world : World} (hw : world.WellFormed)
    {cell : Heap.Cell} {value : Value} {owners : List Nat} (h : Rep world.memory cell (Slot.ofValue value) owners)
    (ho : BoxOwners world owners) (hl : AliveOn world.live owners)
    {frame : Nat} {roots : Roots} {state : State} {guards : List Nat} (hf : Frame world frame roots state guards) :
    run body (fuel + 1) .boxNew [value] = some (.boxed value, Cost.entry .boxNew) ∧
      Rep (world.allocate .box cell).memory (.owned world.memory.length) (Slot.ofValue (.boxed value))
        (owners ++ [world.memory.length]) ∧
      BoxOwners (world.allocate .box cell) (owners ++ [world.memory.length]) ∧
      AliveOn (world.allocate .box cell).live (owners ++ [world.memory.length]) ∧
      Frame (world.allocate .box cell) frame roots state guards := by
  have hk := world.allocate_keeps hw .box cell owners
  refine ⟨rfl, ?_, BoxOwners.allocate hw ho cell, ?_, hf.keep (world.allocate_keeps hw .box cell guards)⟩
  · simpa only [World.allocate, Heap.alloc, Slot.ofValue] using h.alloc
  · intro address ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hk.alive address ha (hl address ha)
    · simpa only [List.mem_singleton.mp ha] using (world.allocate_spec .box cell).2.2.2.1

/-- The guard list comes from a retained caller frame's actual live reference
graphs. A complete trace must still prove the dropping action's disjointness. -/
theorem action_drop_frame {world : World} {raw : Heap.Locals} {state : State} {owners : OwnerState}
    (h : EnvRep world.memory raw state owners) (call : Calls) (slot : Nat)
    {frame : Nat} {roots : Roots} {caller : State} {guards : List Nat}
    (hf : Frame world frame roots caller guards) (hl : AliveOn world.live (owners slot)) (hn : (owners slot).Nodup)
    (hs : ∀ address ∈ guards, address ∉ owners slot) :
    action call state (.drop slot) = some (state.set slot .empty, Cost.local 1 (state slot).dropWork) ∧
      destroyLocal world.memory (raw slot) (state slot) = some (owners slot, (state slot).dropWork) ∧
      Frame (world.retire (owners slot)) frame roots caller guards ∧
      (∀ address ∈ owners slot, world.live address = true ∧ (world.retire (owners slot)).live address = false) := by
  have hd := action_drop_retire h call slot hl hn hs hf.alive
  exact ⟨hd.2.1, hd.1, hf.retire hs, hd.2.2.2.2.2.1⟩

end SubtreeProofs.Rust.SourceEval.AddressedPrimitives
