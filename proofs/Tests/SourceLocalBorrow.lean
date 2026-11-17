import SubtreeProofs.Rust.SourceEvalLocalBorrow

namespace SourceLocalBorrowTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage

-- One Box, one partially moved local and a caller containing a nested shared
-- reference into that local. The caller's graph must retain both roots 0/1.
private def memory : Memory := [.number 7,
  .node .tuple 0 [.number 3, .owned 0, .shared ⟨0, []⟩], .shared ⟨1, [2]⟩]
private def world : World := ⟨memory, fun address =>
  if address = 0 then some .box else if address = 1 then some (.stack 10 0 0)
  else if address = 2 then some (.stack 20 0 0) else none,
  fun address => decide (address < 3)⟩
private def roots : Roots := fun slot => if slot = 0 then some ⟨1, 0⟩ else none
private def callerRoots : Roots := fun slot => if slot = 0 then some ⟨2, 0⟩ else none
private def mask : Slot := .node .tuple 0 [.empty, .boxed (.number 7), .shared (.number 7)]
private def state : Partial.Locals := fun slot => if slot = 0 then mask else .empty
private def caller : Partial.Locals := fun slot => if slot = 0 then .shared (.reference (.number 7)) else .empty
private theorem number_graph : Graph memory (.number 7) (.number 7) [] := .number 7
private theorem reference_graph : Graph memory (.shared ⟨0, []⟩) (.reference (.number 7)) [0] :=
  .shared (by rfl) number_graph
private theorem partial_graph : PartialGraph memory
    (.node .tuple 0 [.number 3, .owned 0, .shared ⟨0, []⟩]) mask [0, 0] :=
  .node (.cons (.empty _) (.cons (.owned (by rfl) (.number 7)) (.cons (.shared reference_graph) .nil)))
private theorem caller_graph : PartialGraph memory (.shared ⟨1, [2]⟩)
    (.shared (.reference (.number 7))) [0, 1] :=
  .shared (.shared (by rfl) reference_graph)

private theorem well_formed : world.WellFormed := by
  constructor
  · intro address
    by_cases h₀ : address = 0
    · simp [world, memory, h₀]
    · by_cases h₁ : address = 1
      · simp [world, memory, h₁]
      · by_cases h₂ : address = 2
        · simp [world, memory, h₂]
        · simp [world, memory, h₀, h₁, h₂]
          omega
  · intro address hl
    have hh : address < 3 := by simpa only [world, decide_eq_true_eq] using hl
    exact hh

private theorem frame : Frame world 10 roots state [0, 0, 1] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact ⟨_, [0, 0], rfl, rfl, partial_graph, List.Subset.refl _⟩
  · simp only [roots, state, hz, ite_false]

private theorem caller_frame : Frame world 20 callerRoots caller [0, 1, 2] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact ⟨_, [0, 1], rfl, rfl, caller_graph, List.Subset.refl _⟩
  · simp only [callerRoots, caller, hz, ite_false]

-- A moved sibling is rejected even though raw memory still contains its bits.
example : state.read (.field (.local 0) none 0) = none := by
  simp [state, mask, Partial.Locals.read, splitPlace, Slot.read, Slot.get, Slot.materialize]
example : Heap.read memory ⟨1, [0]⟩ = some (.number 3) := rfl
example : state.read (.local 0) = none := by
  simp [state, mask, Partial.Locals.read, splitPlace, Slot.read, Slot.get, Slot.materialize, materializeFields]

-- A surviving field can be addressed without fully materializing its parent.
example : ∃ pointer used,
    Storage.borrow world roots (.field (.local 0) none 1) = some (.shared pointer) ∧
    Loan world pointer (.boxed (.number 7)) used ∧ used ++ [pointer.root] ⊆ [0, 0, 1] :=
  frame.borrow _ (by simp [state, mask, Partial.Locals.read, splitPlace, Slot.read, Slot.get, Slot.materialize])

example : SourceEval.expression state (.address (.field (.local 0) none 1)) =
    some (.reference (.boxed (.number 7)), state) ∧
    ∃ pointer used, Storage.borrow world roots (.field (.local 0) none 1) = some (.shared pointer) ∧
      Loan world pointer (.boxed (.number 7)) used ∧
      Readable memory world.live (.shared pointer) (.reference (.boxed (.number 7))) ∧
      used ++ [pointer.root] ⊆ [0, 0, 1] :=
  SourceEval.AddressedPrimitives.expression_address frame _
    (by simp [state, mask, Partial.Locals.read, splitPlace, Slot.read, Slot.get, Slot.materialize])

-- Both owned and shared reborrows retain the same concrete Box root.
example : Storage.borrow world roots (.deref (.field (.local 0) none 1)) = some (.shared ⟨0, []⟩) := rfl
example : Storage.borrow world roots (.deref (.field (.local 0) none 2)) = some (.shared ⟨0, []⟩) := rfl
example : Storage.borrow world callerRoots (.deref (.deref (.local 0))) = some (.shared ⟨0, []⟩) := rfl

-- Allocation supplies a distinct stack storage root; its proof also checks the
-- target was absent, rather than silently clobbering a live local binding.
example : state 1 = .empty ∧
    Frame (world.allocate (.stack 10 1 4) (.number 19)) 10
      (roots.set 1 (some ⟨memory.length, 4⟩)) (state.set 1 (.number 19))
      ([0, 0, 1] ++ [] ++ [memory.length]) :=
  frame.allocate well_formed (slot := 1) rfl 4 (.number 19) (by simp [AliveOn])

example : (world.allocate (.stack 10 1 4) (.number 19)).WellFormed := well_formed.allocate _ _
example : (world.retire [0]).WellFormed := well_formed.retire _
example : BoxOwners world [0] := by simp [BoxOwners, world]
example : (world.retire [0]).live 1 = world.live 1 :=
  BoxOwners.retire_stack (owners := [0]) (by simp [BoxOwners, world]) (by rfl)

-- Ending storage invalidates reads through it even while its data is retained.
example : readLive (world.retire [1]).memory (world.retire [1]).live ⟨1, [1]⟩ = none := by
  exact readLive_retired _ _ _ _ (by simp)
example : Heap.read (world.retire [1]).memory ⟨1, [1]⟩ = some (.owned 0) := rfl
example : ¬ Loan (world.retire [1]) ⟨1, [1]⟩ (.boxed (.number 7)) [0] := by
  intro h
  exact h.root_not_retired (by simp)

-- Checking only the outer stack root misses a retired transitive Box target.
example : (world.retire [0]).live 2 = true := rfl
example : ¬ Loan (world.retire [0]) ⟨2, []⟩ (.reference (.reference (.number 7))) [0, 1] := by
  intro h
  have hh := h.alive 0 (by simp)
  change false = true at hh
  cases hh
example : ¬ (∀ address ∈ ([0, 1, 2] : List Nat), address ∉ ([0] : List Nat)) := by simp

-- A callee allocates/drops a fresh Box. The caller retains its actual nested
-- references and stack roots, so every reborrow still works after retirement.
private def extended : World := world.allocate .box (.number 11)
private def raw : Heap.Locals := fun slot => if slot = 0 then some (.owned 3) else none
private def callee : SourceEval.State := fun slot => if slot = 0 then .boxed (.number 11) else .empty
private def owners : OwnerState := fun slot => if slot = 0 then [3] else []
private theorem callee_rep : Partial.Addressed.EnvRep extended.memory raw callee owners := by
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact .stored (.owned (by rfl) (.number 11))
  · simp only [raw, callee, owners, hz, ite_false]
    exact .empty
private theorem retained : Frame extended 20 callerRoots caller [0, 1, 2] :=
  caller_frame.keep (world.allocate_keeps well_formed .box (.number 11) _)

example (calls : SourceEval.Calls) :
    SourceEval.action calls callee (.drop 0) = some (callee.set 0 .empty, SourceEval.Cost.local 1 (callee 0).dropWork) ∧
      destroyLocal extended.memory (raw 0) (callee 0) = some (owners 0, (callee 0).dropWork) ∧
      Frame (extended.retire (owners 0)) 20 callerRoots caller [0, 1, 2] ∧
      (∀ address ∈ owners 0, extended.live address = true ∧ (extended.retire (owners 0)).live address = false) :=
  SourceEval.AddressedPrimitives.action_drop_frame callee_rep calls 0 retained
    (by simp [AliveOn, owners, extended, world, World.allocate, memory]) (by decide +kernel)
    (by simp [owners])

example : ∃ pointer used, Storage.borrow (extended.retire [3]) callerRoots (.deref (.deref (.local 0))) = some (.shared pointer) ∧
    Loan (extended.retire [3]) pointer (.number 7) used ∧ used ++ [pointer.root] ⊆ [0, 1, 2] :=
  (retained.retire (discarded := [3]) (by simp)).borrow _
    (by simp [caller, Partial.Locals.read, splitPlace, Slot.read, Slot.get, Slot.ofValue, Slot.materialize])


example (body : SourceEval.Function → SourceEval.Code) (fuel : Nat) :
    Frame extended 20 callerRoots caller [0, 1, 2] ∧ BoxOwners extended [3] := by
  have h := SourceEval.AddressedPrimitives.box_new_frame body fuel well_formed
    (value := .number 11) (owners := [])
    (by simpa only [Slot.ofValue] using Rep.number (memory := world.memory) 11)
    (by simp [BoxOwners]) (by simp [AliveOn]) caller_frame
  exact ⟨h.2.2.2.2, h.2.2.1⟩

example : ∃ pointer used cell,
    Storage.borrow world roots (.field (.local 0) none 1) = some (.shared pointer) ∧
    Loan world pointer (.boxed (.number 7)) used ∧
    readLive memory world.live pointer = some cell ∧ Typed memory cell (.owned .u32) ∧
    Typed memory (.shared pointer) (.shared (.owned .u32)) := by
  obtain ⟨pointer, used, hb, hl, _⟩ := frame.borrow (.field (.local 0) none 1) (value := .boxed (.number 7))
    (by simp [state, mask, Partial.Locals.read, splitPlace, Slot.read, Slot.get, Slot.materialize])
  obtain ⟨cell, hr, ht, hs⟩ := hl.typed (ty := .owned .u32) (.owned (.number (value := 7) (by decide +kernel)))
  exact ⟨pointer, used, cell, hb, hl, hr, ht, hs⟩

end SourceLocalBorrowTests
