import SubtreeProofs.Rust.SourceRecursiveHelperCallTotality
import SubtreeProofs.Rust.SourceAssignmentTotality
import SubtreeProofs.Rust.SourceEvalAddressedCompleteness

namespace SourceAddressedExpressionTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage

private def tuple : Cell := .node .tuple 0 [.owned 0, .number 9]
private def tupleValue : Value := .node .tuple 0 [.boxed (.number 7), .number 9]
private def whole : Slot := .node .tuple 0 [.boxed (.number 7), .number 9]
private def remaining : Slot := .node .tuple 0 [.boxed .empty, .number 9]
private def memory : Memory := [.number 7, .number 3, tuple, .shared ⟨2, [1]⟩, .node .tuple 0 [], .shared ⟨1, []⟩]
private def world : World := ⟨memory, fun a =>
  if a = 0 then some .box else if a < 5 then some (.stack 10 (a - 1) 0)
  else if a = 5 then some (.stack 20 0 0) else none, fun a => decide (a < 6)⟩
private def roots : Roots := fun slot => if slot < 4 then some ⟨slot + 1, 0⟩ else none
private def state : SourceEval.State := fun slot =>
  if slot = 0 then .number 3 else if slot = 1 then whole else if slot = 2 then .shared (.number 9) else .empty
private def callerRoots : Roots := fun slot => if slot = 0 then some ⟨5, 0⟩ else none
private def caller : SourceEval.State := fun slot => if slot = 0 then .shared (.number 3) else .empty
private def blocked : List Nat := [1, 2, 5]
private def retained : List Nat := [0, 1, 2, 3, 5]
private def payload : Place := .deref (.field (.local 1) none 0)
private def moved := state.set 1 remaining

private theorem tuple_graph : PartialGraph memory tuple whole [0] :=
  .node (.cons (.owned (by rfl) (.number 7)) (.cons (.number 9) .nil))
private theorem rest_graph : PartialGraph memory tuple remaining [0] :=
  .node (.cons (.owned (by rfl) (.empty _)) (.cons (.number 9) .nil))

private theorem well_formed : world.WellFormed := by
  constructor
  · intro a
    by_cases h₀ : a = 0
    · simp [world, memory, h₀]
    · by_cases hl : a < 5
      · simp [world, memory, h₀, hl]
        omega
      · by_cases h₅ : a = 5
        · simp [world, memory, h₅]
        · simp [world, memory, h₀, hl, h₅]
          omega
  · intro a hl
    exact (by simpa only [world, decide_eq_true_eq] using hl : a < 6)

private theorem frame : Frame world 10 roots state [0, 1, 2, 3, 4] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hl : slot < 4
  · rcases (by omega : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3) with rfl | rfl | rfl | rfl
    · exact ⟨_, [], rfl, rfl, .number 3, by simp⟩
    · exact ⟨_, [0], rfl, rfl, tuple_graph, by simp⟩
    · exact ⟨_, [2], rfl, rfl, .shared (.shared (by rfl) (.number 9)), by simp⟩
    · exact ⟨_, [], rfl, rfl, .empty _, by simp⟩
  · simp [roots, state, hl, show slot ≠ 0 by omega, show slot ≠ 1 by omega, show slot ≠ 2 by omega]

private theorem context : Frame world 10 (roots.set 3 none) (state.set 3 .empty) retained := by
  refine ⟨by simp [AliveOn, retained, world], ?_⟩
  intro slot
  by_cases h₃ : slot = 3
  · subst slot; simp [Roots.set, Partial.Locals.set]
  · simp only [Roots.set, Partial.Locals.set, h₃, ite_false]
    by_cases hl : slot < 4
    · rcases (by omega : slot = 0 ∨ slot = 1 ∨ slot = 2) with rfl | rfl | rfl
      · exact ⟨_, [], rfl, rfl, .number 3, by simp [retained]⟩
      · exact ⟨_, [0], rfl, rfl, tuple_graph, by simp [retained]⟩
      · exact ⟨_, [2], rfl, rfl, .shared (.shared (by rfl) (.number 9)), by simp [retained]⟩
    · simp [roots, state, hl, show slot ≠ 0 by omega, show slot ≠ 1 by omega, show slot ≠ 2 by omega]

private theorem caller_frame : Frame world 20 callerRoots caller [1, 5] := by
  refine ⟨by simp [AliveOn, world], ?_⟩
  intro slot
  by_cases hz : slot = 0
  · subst slot
    exact ⟨_, [1], rfl, rfl, .shared (.shared (by rfl) (.number 3)), by simp⟩
  · simp [callerRoots, caller, hz]

private theorem source_move : state.move payload = some (.number 7, moved) := by
  simp [Partial.Locals.move, payload, splitPlace, state, whole, remaining, moved, Slot.take,
    Slot.materialize]

private theorem concrete_move : SourceEval.Addressed.operand world roots blocked state (.move payload) =
    some ((.number 7, .number 7), moved) :=
  SourceEval.Addressed.operand_move_iff.mpr ⟨⟨0, []⟩, source_move, rfl, by simp [blocked]⟩

example : ∃ used, SourceEval.operand state (.move payload) = some (.number 7, moved) ∧
    Graph memory (.number 7) (.number 7) used ∧ used ⊆ [0, 1, 2, 3, 4] ∧
    Frame world 10 roots moved [0, 1, 2, 3, 4] := SourceEval.Addressed.operand_spec frame concrete_move

-- The payload move retains its containing Box's root and raw stored data.
example : destroy memory tuple remaining = some ([0], ⟨3, 1⟩) := by decide +kernel
example : ownedProjection memory tuple [.field none 0, .deref] = some (.number 7) := rfl
example : SourceEval.Addressed.operand world roots blocked moved (.move payload) = none := by
  simp [SourceEval.Addressed.operand, Partial.Locals.move, moved, payload, splitPlace,
    Partial.Locals.set, remaining, Slot.take, Slot.materialize]
example : SourceEval.Addressed.operand world roots [0] state (.move payload) = none := by
  simp [SourceEval.Addressed.operand, Storage.locate, roots, world, memory,
    tuple, payload, splitPlace, locatePath]

-- Copies preserve initialization and concrete reference identities; owned
-- aggregates and Box pointers cannot be copied by this source fragment.
example : SourceEval.Addressed.operand world roots blocked state (.copy (.local 1)) = none := by
  simp [SourceEval.Addressed.operand, SourceEval.Addressed.read, SourceEval.Addressed.copyCell,
    Partial.Locals.read, state, whole, splitPlace, Slot.read, Slot.get, Slot.materialize,
    materializeFields, Storage.locate, roots, world, memory, tuple, locatePath]
example : SourceEval.Addressed.operand world roots blocked state (.number (2^32)) = none := by
  simp only [SourceEval.Addressed.operand, lt_self_iff_false, ite_false]

private def comparison : SourceEval.Expr := .less (.copy (.local 0)) (.number 8)
private theorem compared : SourceEval.Addressed.expression world roots blocked state comparison =
    some ((.boolean true, .boolean true), state) := by
  simp [comparison, SourceEval.Addressed.expression, SourceEval.Addressed.operand, SourceEval.Addressed.read,
    SourceEval.Addressed.copyCell, Partial.Locals.read, splitPlace, state, Slot.read, Slot.get,
    Slot.materialize, Storage.locate, roots, world, memory, locatePath, SourceEval.less32]

private def aggregateRhs : SourceEval.Expr :=
  .aggregate .tuple 0 [.move payload, .copy (.deref (.local 2)), .number 4]
private def aggregateCell : Cell := .node .tuple 0 [.number 7, .number 9, .number 4]
private def aggregateValue : Value := .node .tuple 0 [.number 7, .number 9, .number 4]
private theorem aggregated : SourceEval.Addressed.expression world roots blocked state aggregateRhs =
    some ((aggregateCell, aggregateValue), moved) := by
  simp only [aggregateRhs, SourceEval.Addressed.expression, SourceEval.Addressed.operands,
    concrete_move, Bind.bind, Option.bind]
  simp [SourceEval.Addressed.operand, SourceEval.Addressed.read, SourceEval.Addressed.copyCell,
    aggregateCell, aggregateValue, moved, state, Partial.Locals.read, splitPlace,
    Partial.Locals.set, Slot.read, Slot.get, Slot.ofValue, Slot.materialize,
    Storage.locate, roots, world, memory, Heap.read, Heap.fields, tuple, locatePath]

example : SourceEval.expression state aggregateRhs = some (aggregateValue, moved) ∧
    Readable memory world.live aggregateCell aggregateValue ∧ Frame world 10 roots moved [0, 1, 2, 3, 4] :=
  SourceEval.Addressed.expression_readable frame aggregated

-- Evaluation is sequential: a second move sees the first move's hole.
example : SourceEval.Addressed.operands world roots blocked state [.move payload, .move payload] = none := by
  simp only [SourceEval.Addressed.operands, concrete_move, Bind.bind, Option.bind]
  simp [SourceEval.Addressed.operand, Partial.Locals.move, moved, payload, splitPlace,
    Partial.Locals.set, remaining, Slot.take, Slot.materialize]

example : ∃ cell, SourceEval.Addressed.expression world roots blocked state comparison =
    some ((cell, .boolean true), state) := by
  apply SourceEval.Addressed.expression_complete frame (SourceEval.Addressed.expression_readable frame compared).1
  exact ⟨trivial, trivial⟩
example : SourceEval.expression state comparison = some (.boolean true, state) ∧
    Readable memory world.live (.boolean true) (.boolean true) ∧ Frame world 10 roots state [0, 1, 2, 3, 4] :=
  SourceEval.Addressed.expression_readable frame compared

private def reborrow : SourceEval.Expr := .address (.deref (.local 2))
private theorem borrowed : SourceEval.Addressed.expression world roots blocked state reborrow =
    some ((.shared ⟨2, [1]⟩, .reference (.number 9)), state) := by
  simp [reborrow, SourceEval.Addressed.expression, Partial.Locals.read, splitPlace, state,
    Slot.read, Slot.get, Slot.ofValue, Slot.materialize, Storage.borrow, Storage.locate,
    roots, world, memory, Heap.read, Heap.fields, locatePath, tuple]

example : traceGraph memory (.shared ⟨2, [1]⟩) (.reference (.number 9)) = some [2] := by
  simp [traceGraph, memory, Heap.read, Heap.fields, tuple]
example : traceGraph memory (.number 3) (.number 4) = none := by simp [traceGraph]
example : traceGraph memory tuple tupleValue = some [0] := by simp [traceGraph, traceGraphFields, tuple, tupleValue, memory]

private theorem assigned : SourceEval.Addressed.assign world roots 10 blocked retained state 3 reborrow =
    some (world.write 4 (.shared ⟨2, [1]⟩), state.set 3 (Slot.ofValue (.reference (.number 9)))) := by
  apply SourceEval.Addressed.assign_complete (slot := 3) (binding := ⟨4, 0⟩) (used := [2]) frame well_formed borrowed
  · rfl
  · rfl
  · simp [traceGraph, world, memory, Heap.read, Heap.fields, tuple]
  · simp [retained]

example (call : SourceEval.Calls) : ∃ (cell : Cell) (value : Value) (middle : SourceEval.State) (used : List Nat) (binding : Binding),
    SourceEval.Addressed.expression world roots blocked state reborrow = some ((cell, value), middle) ∧
    roots 3 = some binding ∧
    SourceEval.action call state (.assign 3 reborrow) =
      some (state.set 3 (Slot.ofValue (.reference (.number 9))), SourceEval.Cost.local (SourceEval.Action.assign 3 reborrow).weight) ∧
    world.write 4 (.shared ⟨2, [1]⟩) = world.write binding.address cell ∧
    state.set 3 (Slot.ofValue (.reference (.number 9))) = middle.set 3 (Slot.ofValue value) ∧
    Frame (world.write 4 (.shared ⟨2, [1]⟩)) 10 roots (state.set 3 (Slot.ofValue (.reference (.number 9))))
      (retained ++ used ++ [binding.address]) ∧
    Graph (world.write 4 (.shared ⟨2, [1]⟩)).memory cell value used ∧
    Preserves world (world.write 4 (.shared ⟨2, [1]⟩)) retained ∧ (world.write 4 (.shared ⟨2, [1]⟩)).WellFormed := by
  apply SourceEval.Addressed.assign_spec frame well_formed call reborrow ?_ assigned
  intro cell value middle hr
  rw [borrowed] at hr
  have hh := Option.some.inj hr
  simp only [Prod.mk.injEq] at hh
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hh
  exact context

example : Frame (world.write 4 (.shared ⟨2, [1]⟩)) 20 callerRoots caller [1, 5] :=
  caller_frame.write (address := 4) (by simp) _

-- Forward assignment derives its actual context and permits shared aliases.
private def activation : Activation := ⟨10, 4, roots, state⟩
private def suspendedCaller : Activation := ⟨20, 1, callerRoots, caller⟩
private theorem activation_valid : activation.Valid world :=
  ⟨by intro slot hs; change 4 ≤ slot at hs; simp [activation, roots, show ¬ slot < 4 by omega], _, frame⟩
private theorem suspended_valid : suspendedCaller.Valid world :=
  ⟨by intro slot hs; change 1 ≤ slot at hs; simp [suspendedCaller, callerRoots, show slot ≠ 0 by omega], _, caller_frame⟩
private theorem caller_resources : Callers world [suspendedCaller] ⟨[1, 5], [], [1]⟩ :=
  scanCallers_spec (by simpa using suspended_valid) (by decide +kernel)
private theorem roots_separate : activation.RootsSeparate [suspendedCaller] := by
  intro slot binding hb current hm other target ht equality
  have same : current = suspendedCaller := by simpa only [List.mem_singleton] using hm
  subst current
  obtain ⟨_, _, _, first, _, _⟩ := frame.get hb
  obtain ⟨_, _, _, second, _, _⟩ := caller_frame.get ht
  rw [equality] at first
  cases first.symm.trans second
private theorem global_frame : OwnerFrame world
    (activation.owners world ++ (callerOwners world [suspendedCaller] ++ [])) := by
  rw [show activation.owners world ++ (callerOwners world [suspendedCaller] ++ []) = [0] by decide +kernel]
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro a ha; have zero := List.mem_singleton.mp ha; subst a; rfl
  · intro a ha; have zero := List.mem_singleton.mp ha; subst a; rfl
private theorem global_coverage : BoxCoverage world
    (activation.owners world ++ (callerOwners world [suspendedCaller] ++ [])) := by
  rw [show activation.owners world ++ (callerOwners world [suspendedCaller] ++ []) = [0] by decide +kernel]
  intro a hc _
  by_cases hz : a = 0
  · simp [hz]
  · simp only [world, hz, ite_false] at hc
    split_ifs at hc <;> cases hc
private theorem root_permission : SourceEval.Addressed.Derived.RootLoansAllowed world activation [suspendedCaller] 3 ⟨4, 0⟩ := by
  intro remainder suspended inventory callers forbidden
  have actual : activation.scanExcept world 3 = some (⟨[1, 0, 2, 2, 3], [0], [2]⟩ : Resources) := by decide +kernel
  have first := Option.some.inj (inventory.inspect.symm.trans actual)
  have second := callers.unique caller_resources
  cases first
  cases second
  simp at forbidden
private theorem reborrow_any (guarded : List Nat) : SourceEval.Addressed.expression world roots guarded state reborrow =
    some ((.shared ⟨2, [1]⟩, .reference (.number 9)), state) := by
  simpa only [reborrow, SourceEval.Addressed.expression] using borrowed
private theorem payload_permission : SourceEval.Addressed.Derived.PacketLoansAvoid world
    (.shared ⟨2, [1]⟩, .reference (.number 9)) 4 := by
  intro loans footprint member
  simp only [Slot.ofValue] at footprint
  cases footprint with
  | shared graph =>
    have actual : Graph world.memory (.shared ⟨2, [1]⟩) (.reference (.number 9)) [2] := .shared rfl (.number 9)
    rw [graph.guards_unique actual] at member
    simp at member

example : ∃ cell, SourceEval.Addressed.Derived.assign world activation [suspendedCaller] 3 reborrow =
      some (world.write 4 cell, {activation with state := state.set 3 (Slot.ofValue (.reference (.number 9)))}) ∧
    SourceEval.Addressed.Derived.Step world activation [suspendedCaller] (.assign 3 reborrow) (world.write 4 cell)
      {activation with state := state.set 3 (Slot.ofValue (.reference (.number 9)))}
      (SourceEval.Cost.local (SourceEval.Action.assign 3 reborrow).weight) ∧
    OwnerFrame (world.write 4 cell)
      (({activation with state := state.set 3 (Slot.ofValue (.reference (.number 9)))} : Activation).owners (world.write 4 cell) ++
        (callerOwners (world.write 4 cell) [suspendedCaller] ++ [])) ∧
    BoxCoverage (world.write 4 cell)
      (({activation with state := state.set 3 (Slot.ofValue (.reference (.number 9)))} : Activation).owners (world.write 4 cell) ++
        (callerOwners (world.write 4 cell) [suspendedCaller] ++ [])) := by
  apply SourceEval.Addressed.Derived.assign_total (slot := 3) (binding := ⟨4, 0⟩)
    (value := .reference (.number 9)) (middle := state) activation_valid (by simpa using suspended_valid) well_formed
    roots_separate global_frame global_coverage (by rfl) (SourceEval.Addressed.expression_readable frame borrowed).1 (by rfl)
  · intro current suspended _ _; trivial
  · exact root_permission
  · intro current suspended _ _ packet masks run
    change SourceEval.Addressed.expression world roots (current.loans ++ suspended.reads) state reborrow = some (packet, masks) at run
    rw [reborrow_any] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj run)
    exact payload_permission

-- The selected owned payload root is unborrowed even though an inline sibling
-- and the caller's scalar have live shared aliases.
private theorem payload_allowed : SourceEval.Addressed.Allowed world roots ([2] ++ [1, 5]) (.move payload) := by
  apply SourceEval.Addressed.move_allowed_from_loans (current := ⟨[], [], [2]⟩)
    activation_valid roots_separate global_frame caller_resources source_move
  intro cell target located
  have actual : Storage.locate world roots payload = some (.number 7, ⟨0, []⟩) := rfl
  change Storage.locate world roots payload = some (cell, target) at located
  rw [actual] at located
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj located)
  decide +kernel

-- A shared packet that points back into its destination fails the independent
-- loan condition, even though it carries no Box owners.
example : ¬ SourceEval.Addressed.Derived.PacketLoansAvoid world
    (.shared ⟨4, []⟩, .reference (.node .tuple 0 [])) 4 := by
  intro allowed
  have represented : BorrowFootprint world.memory (.shared ⟨4, []⟩) (Slot.ofValue (.reference (.node .tuple 0 []))) [4] := by
    simpa only [Slot.ofValue] using
      (BorrowFootprint.shared (.shared rfl (.node .nil)) : BorrowFootprint world.memory (.shared ⟨4, []⟩) (.shared (.node .tuple 0 [])) [4])
  exact allowed [4] represented (by simp)

-- A complete recursive Box call is constructed from the source payload move.
-- The old Box shell, inline sibling loan and suspended scalar alias coexist
-- with the fresh returned Box; no successful helper call or store is supplied.
example : ∃ minimumFuel minimumBudget final after cost,
    after.Valid final ∧ final.WellFormed ∧
    OwnerFrame final (after.owners final ++ (callerOwners final [suspendedCaller] ++ [])) ∧
    BoxCoverage final (after.owners final ++ (callerOwners final [suspendedCaller] ++ [])) ∧
    ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
      SourceEval.Addressed.Derived.call (SourceEval.Addressed.Recursive.original budget fuel)
        world activation [suspendedCaller] .boxNew [.move payload] 3 = some (final, after, cost) ∧
      SourceEval.action (SourceEval.run SourceEval.Certificate.original.body fuel) state (.call .boxNew [.move payload] 3) =
        some (after.state, cost) := by
  have permission : SourceEval.Addressed.Derived.RootLoansAllowed world {activation with state := moved}
      [suspendedCaller] 3 ⟨4, 0⟩ := by
    intro remainder suspended inventory callers forbidden
    have actual : ({activation with state := moved} : Activation).scanExcept world 3 =
        some (⟨[1, 0, 2, 2, 3], [0], [2]⟩ : Resources) := by decide +kernel
    have first := Option.some.inj (inventory.inspect.symm.trans actual)
    have second := callers.unique caller_resources
    cases first
    cases second
    simp at forbidden
  have moves : ∀ current suspended, Scanned world activation current → Callers world [suspendedCaller] suspended →
      ∀ op ∈ ([.move payload] : List SourceEval.Operand),
        SourceEval.Addressed.Allowed world roots (current.loans ++ suspended.reads) op := by
    intro current suspended scan callers op member
    have actual : activation.scan world = some (⟨[1, 0, 2, 2, 3, 4], [0], [2]⟩ : Resources) := by decide +kernel
    have same := Option.some.inj (scan.scan.symm.trans actual)
    have old := callers.unique caller_resources
    cases same
    cases old
    have eq : op = .move payload := by simpa only [List.mem_singleton] using member
    subst op
    exact payload_allowed
  obtain ⟨minimumFuel, minimumBudget, final, after, cost, valid, wf, _, frame, coverage, stable⟩ :=
    SourceEval.Addressed.Recursive.original_helper_call_stable (slot := 3) (binding := ⟨4, 0⟩)
      (values := [.number 7]) (masks := moved) (types := [.u32]) (ty := .owned .u32)
      activation_valid (by simpa using suspended_valid) well_formed roots_separate global_frame global_coverage
      .boxNew rfl [.move payload] rfl
      (by simp only [activation, SourceEval.operands, SourceEval.operand, source_move, bind, Option.bind])
      (by rfl) (.cons (.number (by decide +kernel)) .nil) rfl (.owned .u32) moves permission
  exact ⟨minimumFuel, minimumBudget, final, after, cost, valid, wf, frame, coverage, stable⟩

end SourceAddressedExpressionTests
