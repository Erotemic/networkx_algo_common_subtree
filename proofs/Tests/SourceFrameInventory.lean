import SubtreeProofs.Rust.SourceEvalDerivedAssignments

namespace SourceFrameInventoryTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage

private def tuple : Cell := .node .tuple 0 [.owned 0, .number 9]
private def whole : Slot := .node .tuple 0 [.boxed (.number 7), .number 9]
private def rest : Slot := .node .tuple 0 [.boxed .empty, .number 9]
private def memory : Memory := [.number 7, tuple, .shared ⟨1, [1]⟩, .node .tuple 0 [], .shared ⟨0, []⟩]
private def world : World := ⟨memory, fun a =>
  if a = 0 then some .box else if a < 4 then some (.stack 10 (a - 1) 0)
  else if a = 4 then some (.stack 20 0 0) else none, fun a => decide (a < 5)⟩
private def roots : Roots := fun slot => if slot < 3 then some ⟨slot + 1, 0⟩ else none
private def state : SourceEval.State := fun slot => if slot = 0 then whole else if slot = 1 then .shared (.number 9) else .empty
private def active : Activation := ⟨10, 3, roots, state⟩
private def callerRoots : Roots := fun slot => if slot = 0 then some ⟨4, 0⟩ else none
private def callerState : SourceEval.State := fun slot => if slot = 0 then .shared (.number 7) else .empty
private def caller : Activation := ⟨20, 1, callerRoots, callerState⟩
private def payload : Place := .deref (.field (.local 0) none 0)

private theorem tuple_graph : PartialGraph memory tuple whole [0] :=
  .node (.cons (.owned (by rfl) (.number 7)) (.cons (.number 9) .nil))
private theorem active_frame : Frame world 10 roots state [0, 1, 2, 3] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hl : slot < 3
  · rcases (by omega : slot = 0 ∨ slot = 1 ∨ slot = 2) with rfl | rfl | rfl
    · exact ⟨_, [0], rfl, rfl, tuple_graph, by simp⟩
    · exact ⟨_, [1], rfl, rfl, .shared (.shared (by rfl) (.number 9)), by simp⟩
    · exact ⟨_, [], rfl, rfl, .empty _, by simp⟩
  · simp [roots, state, hl, show slot ≠ 0 by omega, show slot ≠ 1 by omega]
private theorem active_valid : active.Valid world :=
  ⟨by intro slot hs; change 3 ≤ slot at hs; simp [active, roots, show ¬slot < 3 by omega], _, active_frame⟩
private theorem caller_frame : Frame world 20 callerRoots callerState [0, 4] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact ⟨_, [0], rfl, rfl, .shared (.shared (by rfl) (.number 7)), by simp⟩
  · simp [callerRoots, callerState, hz]
private theorem caller_valid : caller.Valid world :=
  ⟨by intro slot hs; change 1 ≤ slot at hs; simp [caller, callerRoots, show slot ≠ 0 by omega], _, caller_frame⟩
private theorem well_formed : world.WellFormed := by
  constructor
  · intro a
    by_cases hz : a = 0
    · simp [world, memory, hz]
    · by_cases hl : a < 4
      · simp [world, memory, hz, hl]
        omega
      · by_cases h₄ : a = 4
        · simp [world, memory, h₄]
        · simp [world, memory, hz, hl, h₄]
          omega
  · intro a hl
    exact (by simpa only [world, decide_eq_true_eq] using hl : a < 5)

private def current : Resources := ⟨[0, 1, 1, 2, 3], [0], [1]⟩
private def suspended : Resources := ⟨[0, 4], [], [0]⟩

private theorem current_scan : active.scan world = some current := by
  simp [Activation.scan, active, Storage.inspect, Storage.inspectSlot, List.range_succ, roots, state, world, memory,
    traceResources, traceFieldsResources, traceGraph, whole, tuple,
    Heap.read, Heap.fields, Resources.plus, Resources.atRoot, current]
private theorem caller_scan : caller.scan world = some suspended := by
  simp [Activation.scan, caller, Storage.inspect, Storage.inspectSlot, List.range_succ, callerRoots, callerState, world, memory,
    traceResources, traceGraph, Heap.read, Heap.fields, Resources.plus, Resources.atRoot, suspended]

-- An owned payload is not itself a shared loan; its containing Box remains an
-- owner after a payload move. The independent shared field does protect root 1.
example : traceResources memory tuple whole = some (⟨[0], [0], []⟩ : Resources) := by
  simp [traceResources, traceFieldsResources, tuple, whole, memory, Resources.plus]
example : traceResources memory tuple rest = some (⟨[0], [0], []⟩ : Resources) := by
  simp [traceResources, traceFieldsResources, tuple, rest, memory, Resources.plus]
example : traceResources memory (.shared ⟨0, []⟩) (.shared (.number 7)) = some (⟨[0], [], [0]⟩ : Resources) := by
  simp [traceResources, traceGraph, memory, Heap.read, Heap.fields]
example : Scanned world active current := Activation.scan_spec active_valid current_scan
example : ∃ cell loans, memory[4]? = some cell ∧ BorrowFootprint memory cell (callerState 0) loans ∧ loans ⊆ suspended.loans :=
  (Activation.scan_spec caller_valid caller_scan).loan_coverage 0 rfl
example : current.owners.length = ((List.range active.count).map (fun i => (active.state i).dropWork.boxes)).sum :=
  (Activation.scan_spec active_valid current_scan).inventory.boxes
example : Frame world active.frame (active.roots.set 2 none) (active.state.set 2 .empty) [0, 1, 1, 2] := by
  apply Activation.context_spec active_valid 2 (r := ⟨[0, 1, 1, 2], [0], [1]⟩)
  simp [Activation.scanExcept, active, remainingSlots, Storage.inspect, Storage.inspectSlot, List.range_succ, roots, state, world, memory,
    traceResources, traceFieldsResources, traceGraph, whole, tuple, Heap.read, Heap.fields,
    Resources.plus, Resources.atRoot]

private def rhs : SourceEval.Expr := .address payload
private def after : Activation := { active with state := state.set 2 (Slot.ofValue (.reference (.number 7))) }
private def next := world.write 3 (.shared ⟨0, []⟩)
private theorem derived_run : SourceEval.Addressed.Derived.assign world active [caller] 2 rhs = some (next, after) := by
  simp only [SourceEval.Addressed.Derived.assign, current_scan, scanCallers, caller_scan, Bind.bind, Option.bind]
  simp [SourceEval.Addressed.expression, rhs, SourceEval.Addressed.Derived.store, active, suspended,
    Activation.scanExcept, remainingSlots, Storage.inspect, Storage.inspectSlot, List.range_succ, roots, state, world, memory,
    traceResources, traceFieldsResources, traceGraph, whole, tuple, Heap.read, Heap.fields,
    Resources.plus, Resources.atRoot, Storage.borrow, Storage.locate, locatePath, payload, splitPlace,
    Partial.Locals.read, Slot.read, Slot.get, Slot.materialize, SourceEval.Addressed.emptySlot,
    World.writeStack, next, after]

-- A newly stored reference becomes an active loan in the next state; its
-- target is discovered from the new memory cell and initialized source mask.
example : after.scan next = some (⟨[0, 1, 1, 2, 0, 3], [0], [1, 0]⟩ : Resources) := by
  simp [Activation.scan, after, active, next, World.write, Storage.inspect, Storage.inspectSlot,
    List.range_succ, roots, state, world, memory, Partial.Locals.set, Slot.ofValue,
    traceResources, traceFieldsResources, traceGraph, whole, tuple, Heap.read, Heap.fields,
    Resources.plus, Resources.atRoot]

example (call : SourceEval.Calls) :
    SourceEval.action call active.state (.assign 2 rhs) = some (after.state, SourceEval.Cost.local (SourceEval.Action.assign 2 rhs).weight) ∧
      after.frame = active.frame ∧ after.count = active.count ∧ after.roots = active.roots ∧ after.Valid next ∧
      (∀ a ∈ [caller], a.Valid next) ∧ next.WellFormed ∧
      ∃ r, scanCallers world [caller] = some r ∧ Callers next [caller] r ∧ Preserves world next r.reads :=
  SourceEval.Addressed.Derived.assign_spec active_valid (by simpa using caller_valid) well_formed call 2 rhs derived_run

-- The caller's loan to Box root 0 is discovered without a supplied blocked
-- list. A payload move is rejected; an address/reborrow above remains valid.
example : SourceEval.Addressed.Derived.assign world active [caller] 2 (.use (.move payload)) = none := by
  simp only [SourceEval.Addressed.Derived.assign, current_scan, scanCallers, caller_scan, Bind.bind, Option.bind]
  simp [current, suspended, SourceEval.Addressed.expression, SourceEval.Addressed.operand, Partial.Locals.move, payload,
    splitPlace, active, state, whole, Slot.take, Slot.materialize, Storage.locate, roots, world,
    memory, tuple, locatePath, Resources.plus]

-- Removing that suspended caller removes its loan guard. The actual payload
-- move then succeeds while retaining the Box shell in the active source mask.
private def moved := (state.set 0 rest).set 2 (Slot.ofValue (.number 7))
example : SourceEval.Addressed.Derived.assign world active [] 2 (.use (.move payload)) =
    some (world.write 3 (.number 7), { active with state := moved }) := by
  simp only [SourceEval.Addressed.Derived.assign, current_scan, scanCallers, Bind.bind, Option.bind]
  simp [current, SourceEval.Addressed.expression,
    SourceEval.Addressed.operand, Partial.Locals.move, payload, splitPlace, active, state, whole, rest,
    Slot.take, Slot.materialize, Storage.locate, roots, world, memory, tuple, locatePath,
    Activation.scanExcept, remainingSlots, Storage.inspect, Storage.inspectSlot, List.range_succ, traceResources, traceFieldsResources,
    traceGraph, Heap.read, Heap.fields, Resources.plus, Resources.atRoot, SourceEval.Addressed.Derived.store,
    SourceEval.Addressed.emptySlot, Partial.Locals.set, World.writeStack, moved]

-- Bounds are a necessary input invariant; a truncated slot scan cannot
-- certify an activation which still has a live binding beyond its count.
example : ¬ ({ active with count := 1 } : Activation).Valid world := by
  intro h
  have hh := h.1 1 (by decide +kernel)
  change some (⟨2, 0⟩ : Binding) = none at hh
  cases hh

-- Complete owner occurrences remain separate from allowed shared aliases.
example : traceResources memory (.node .tuple 0 [.owned 0, .owned 0])
    (.node .tuple 0 [.boxed (.number 7), .boxed (.number 7)]) =
    some (⟨[0, 0], [0, 0], []⟩ : Resources) := by
  simp [traceResources, traceFieldsResources, memory, Resources.plus]
example : ¬ ([0, 0] : List Nat).Nodup := by decide +kernel

-- Inspection checks storage identity and every graph root's liveness, including
-- transitive targets rather than only the reference local's own stack root.
example : ({ caller with frame := 21 } : Activation).scan world = none := by
  simp [Activation.scan, caller, Storage.inspect, Storage.inspectSlot, List.range_succ,
    callerRoots, world]
example : caller.scan (world.retire [0]) = none := by
  simp [Activation.scan, caller, Storage.inspect, Storage.inspectSlot, List.range_succ,
    callerRoots, callerState, world, World.retire, retire, memory, traceResources,
    traceGraph, Heap.read, Heap.fields, Resources.atRoot]

end SourceFrameInventoryTests
