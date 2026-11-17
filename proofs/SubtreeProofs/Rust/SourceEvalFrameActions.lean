module

public import SubtreeProofs.Rust.SourceFrameUpdates

/-! Actual source storage markers and assignment continuations use guarded
addressable frames. Assignment consumes the successful RHS result and its
represented intermediate frame; complete addressed RHS/control/callee execution
is not supplied as a hidden parent contract. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.AddressedPrimitives

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem action_storageLive {world : World} {frame : Nat} {roots : Roots} {state : State} {guards : List Nat}
    (hf : Frame world frame roots state guards) (hw : world.WellFormed) (call : Calls) (slot generation : Nat)
    (hn : roots slot = none) :
    action call state (.storageLive slot) = some (state.set slot .empty, Cost.local 1) ∧
      Frame (world.allocate (.stack frame slot generation) (.node .tuple 0 [])) frame
        (roots.set slot (some ⟨world.memory.length, generation⟩)) (state.set slot .empty)
        (guards ++ [] ++ [world.memory.length]) ∧
      (world.allocate (.stack frame slot generation) (.node .tuple 0 [])).WellFormed := by
  have h := hf.allocate hw hn generation (PartialGraph.empty (.node .tuple 0 [])) (by simp [AliveOn])
  exact ⟨rfl, h.2, hw.allocate _ _⟩

theorem action_storageDead {world : World} {frame : Nat} {roots : Roots} {state : State} {all guards : List Nat}
    (hf : Frame world frame roots state all) (hw : world.WellFormed) (call : Calls) (slot : Nat)
    {binding : Binding} (hr : roots slot = some binding) (hempty : state slot = .empty)
    (context : Frame world frame (roots.set slot none) (state.set slot .empty) guards)
    (hs : binding.address ∉ guards) :
    action call state (.storageDead slot) = some (state.set slot .empty, Cost.local 1) ∧
      world.endStack frame slot binding guards = some (world.retire [binding.address]) ∧
      Frame (world.retire [binding.address]) frame (roots.set slot none) (state.set slot .empty) guards ∧
      (state slot).dropWork = {} ∧ (world.retire [binding.address]).live binding.address = false := by
  obtain ⟨_, used, _, hc, _, hsub⟩ := hf.get hr
  have hl := hf.alive binding.address (hsub (List.mem_append_right _ (by simp)))
  exact ⟨rfl, world.endStack_success hw hc hl hs, context.endStorage hs,
    by simp only [hempty, Slot.dropWork], retire_member _ (by simp)⟩

/-- Actual source bodies also end storage of still-initialized shared/scalar
temporaries. No Box owner may disappear; a partial Box shell fails this test. -/
theorem action_storageDead_nonowning {world : World} {frame : Nat} {roots : Roots} {state : State} {all guards : List Nat}
    (hf : Frame world frame roots state all) (hw : world.WellFormed) (call : Calls) (slot : Nat)
    {binding : Binding} (hr : roots slot = some binding) (hzero : (state slot).dropWork.boxes = 0)
    (context : Frame world frame (roots.set slot none) (state.set slot .empty) guards)
    (hs : binding.address ∉ guards) :
    action call state (.storageDead slot) = some (state.set slot .empty, Cost.local 1) ∧
      world.endStack frame slot binding guards = some (world.retire [binding.address]) ∧
      Frame (world.retire [binding.address]) frame (roots.set slot none) (state.set slot .empty) guards ∧
      (state slot).dropWork.boxes = 0 ∧ (world.retire [binding.address]).live binding.address = false := by
  obtain ⟨_, _, _, hc, _, hsub⟩ := hf.get hr
  have hl := hf.alive binding.address (hsub (List.mem_append_right _ (by simp)))
  exact ⟨rfl, world.endStack_success hw hc hl hs, context.endStorage hs, hzero, retire_member _ (by simp)⟩

theorem storageDead_no_owners {memory : Heap.Memory} {raw : Option Heap.Cell} {part : Slot} {owners : List Nat}
    (h : LocalRep memory raw part owners) (hzero : part.dropWork.boxes = 0) : owners = [] :=
  List.eq_nil_of_length_eq_zero (h.boxes.trans hzero)

/-- The represented world/frame is the state after RHS evaluation. This proves
the store continuation and actual source action equality; it does not replace
the remaining addressed evaluation of arbitrary RHS operands/expressions. -/
theorem action_assign_store {world : World} {frame : Nat} {roots : Roots} {state middle : State}
    {all guards used : List Nat} (hf : Frame world frame roots middle all) (hw : world.WellFormed)
    (call : Calls) (slot : Nat) (rhs : Expr) {value : Value}
    (he : expression state rhs = some (value, middle)) {binding : Binding}
    (hr : roots slot = some binding) (hempty : middle slot = .empty)
    (context : Frame world frame (roots.set slot none) (middle.set slot .empty) guards)
    {cell : Heap.Cell} (hg : PartialGraph world.memory cell (Slot.ofValue value) used)
    (ha : AliveOn world.live used) (hs : binding.address ∉ guards ++ used) :
    action call state (.assign slot rhs) = some (middle.set slot (Slot.ofValue value), Cost.local (Action.assign slot rhs).weight) ∧
      world.writeStack frame slot binding (guards ++ used) cell = some (world.write binding.address cell) ∧
      Frame (world.write binding.address cell) frame roots (middle.set slot (Slot.ofValue value))
        (guards ++ used ++ [binding.address]) ∧
      (world.write binding.address cell).memory.length = world.memory.length := by
  obtain ⟨_, _, _, hc, _, hsub⟩ := hf.get hr
  have hl := hf.alive binding.address (hsub (List.mem_append_right _ (by simp)))
  have h := Frame.store hw hr hempty context hc hl hg ha hs
  exact ⟨by simp only [action, he, bind, Option.bind], h.2.1, h.2.2, List.length_set⟩

theorem action_assign_number {world : World} {frame : Nat} {roots : Roots} {state : State}
    {all guards : List Nat} (hf : Frame world frame roots state all) (hw : world.WellFormed)
    (call : Calls) (slot number : Nat) (hb : number < 2^32) {binding : Binding}
    (hr : roots slot = some binding) (hempty : state slot = .empty)
    (context : Frame world frame (roots.set slot none) (state.set slot .empty) guards)
    (hs : binding.address ∉ guards) :
    action call state (.assign slot (.use (.number number))) =
        some (state.set slot (Slot.ofValue (.number number)), Cost.local 2) ∧
      world.writeStack frame slot binding (guards ++ []) (.number number) = some (world.write binding.address (.number number)) ∧
      Frame (world.write binding.address (.number number)) frame roots (state.set slot (Slot.ofValue (.number number)))
        (guards ++ [] ++ [binding.address]) ∧
      (world.write binding.address (.number number)).memory.length = world.memory.length := by
  simpa only [Action.weight, Expr.weight, Operand.weight] using
    (action_assign_store (value := .number number) (used := []) (cell := Heap.Cell.number number)
    hf hw call slot (.use (.number number))
    (by simp only [expression, operand, hb, ↓reduceIte]) hr hempty context
    (by simpa only [Slot.ofValue] using PartialGraph.number (memory := world.memory) number)
    (by simp [AliveOn]) (by simpa only [List.append_nil] using hs))

end SubtreeProofs.Rust.SourceEval.AddressedPrimitives
