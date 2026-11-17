module

public import SubtreeProofs.Rust.SourceHeapWrites

/-! Empty-destination initialization, guarded in-place local writes and stack
storage endpoints. Frame contexts describe the other actual source locals;
resource-safe operand moves and recursive construction of these contexts remain
execution obligations. Clearing a graph view alone is not permission to lose an
owner or invalidate a retained reference. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open LookupSource.Heap

theorem Roots.set_restore {roots : Roots} {slot : Nat} {binding : Binding} (h : roots slot = some binding) :
    (roots.set slot none).set slot (some binding) = roots := by
  funext index
  by_cases hi : index = slot
  · subst index; simp only [Roots.set, ite_true, h]
  · simp only [Roots.set, hi, ite_false]

theorem locals_set_overwrite (state : Partial.Locals) (slot : Nat) (first last : Slot) :
    (state.set slot first).set slot last = state.set slot last := by
  funext index
  by_cases hi : index = slot <;> simp only [Partial.Locals.set, hi, ite_true, ite_false]

theorem Frame.erase {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (slot : Nat) :
    Frame world frame (roots.set slot none) (state.set slot .empty) guards := by
  refine ⟨h.alive, ?_⟩
  intro index
  by_cases hi : index = slot
  · subst index; simp only [Roots.set, Partial.Locals.set, ite_true]
  · simpa only [Roots.set, Partial.Locals.set, hi, ite_false] using h.slots index

theorem Frame.bind {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) {slot : Nat} (hn : roots slot = none) {binding : Binding}
    {cell : Cell} {part : Slot} {used : List Nat}
    (hc : world.memory[binding.address]? = some cell)
    (ht : world.classes binding.address = some (.stack frame slot binding.generation))
    (hg : PartialGraph world.memory cell part used) (hl : AliveOn world.live (used ++ [binding.address])) :
    state slot = .empty ∧ Frame world frame (roots.set slot (some binding)) (state.set slot part)
      (guards ++ used ++ [binding.address]) := by
  refine ⟨by simpa only [hn] using h.slots slot, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact h.alive a ha
      · exact hl a (List.mem_append_left _ ha)
    · exact hl a (List.mem_append_right _ ha)
  · intro index
    by_cases hi : index = slot
    · subst index
      simp only [Roots.set, Partial.Locals.set, ite_true]
      exact ⟨cell, used, hc, ht, hg, fun a ha => by
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (List.mem_append_right _ ha)
        · exact List.mem_append_right _ ha⟩
    · simp only [Roots.set, Partial.Locals.set, hi, ite_false]
      cases hr : roots index with
      | none => simpa only [hr] using h.slots index
      | some old =>
        obtain ⟨raw, all, hc', ht', hg', hs'⟩ := h.get hr
        exact ⟨raw, all, hc', ht', hg', fun _ ha => List.mem_append_left _ (List.mem_append_left _ (hs' ha))⟩

/-- The other locals form an explicit frame. The original destination is
empty, and no retained or RHS graph may refer to the root being overwritten. -/
theorem Frame.store {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {guards used : List Nat} (hw : world.WellFormed) {slot : Nat} {binding : Binding}
    (hr : roots slot = some binding) (hempty : state slot = .empty)
    (context : Frame world frame (roots.set slot none) (state.set slot .empty) guards)
    (hc : world.classes binding.address = some (.stack frame slot binding.generation))
    (hl : world.live binding.address = true) {cell : Cell} {part : Slot}
    (hg : PartialGraph world.memory cell part used) (ha : AliveOn world.live used)
    (hs : binding.address ∉ guards ++ used) :
    state slot = .empty ∧
      world.writeStack frame slot binding (guards ++ used) cell = some (world.write binding.address cell) ∧
      Frame (world.write binding.address cell) frame roots (state.set slot part)
        (guards ++ used ++ [binding.address]) := by
  have hleft : binding.address ∉ guards := fun h => hs (List.mem_append_left _ h)
  have hright : binding.address ∉ used := fun h => hs (List.mem_append_right _ h)
  have hp := world.write_preserves hright cell
  have hb : binding.address < world.memory.length := (hw.1 _).mp (by simp [hc])
  have hframe := context.write hleft cell
  have hh := hframe.bind (slot := slot) (by simp [Roots.set])
    (binding := binding) (world.write_spec hb cell).1 hc (hg.transport hp.reads)
    (by intro a had; rcases List.mem_append.mp had with had | had
        · exact ha a had
        · simpa only [World.write, List.mem_singleton.mp had] using hl)
  refine ⟨hempty, world.writeStack_success hw hc hl hs cell, ?_⟩
  simpa only [Roots.set_restore hr, locals_set_overwrite] using hh.2

def World.endStack (world : World) (frame slot : Nat) (binding : Binding) (guards : List Nat) : Option World :=
  if world.classes binding.address = some (.stack frame slot binding.generation) ∧
      world.live binding.address = true ∧ binding.address < world.memory.length ∧ binding.address ∉ guards then
    some (world.retire [binding.address])
  else none

theorem World.endStack_success {world : World} {frame slot : Nat} {binding : Binding} {guards : List Nat}
    (hw : world.WellFormed) (hc : world.classes binding.address = some (.stack frame slot binding.generation))
    (hl : world.live binding.address = true) (hs : binding.address ∉ guards) :
    world.endStack frame slot binding guards = some (world.retire [binding.address]) := by
  have hb : binding.address < world.memory.length := (hw.1 _).mp (by simp [hc])
  simp [endStack, hc, hl, hb, hs]

theorem Frame.endStorage {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (context : Frame world frame (roots.set slot none) (state.set slot .empty) guards)
    {binding : Binding} (hs : binding.address ∉ guards) :
    Frame (world.retire [binding.address]) frame (roots.set slot none) (state.set slot .empty) guards :=
  context.retire (by intro a ha hb; exact hs (List.mem_singleton.mp hb ▸ ha))

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
