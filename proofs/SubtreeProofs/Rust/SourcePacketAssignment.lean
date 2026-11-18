module

public import SubtreeProofs.Rust.SourceLoanSafeMachine

/-! Construct one guarded assignment with an explicitly constructed physical
RHS packet. This retains shared-pointer identity for later aggregate loan-origin
proofs; scanning, retained inventories, ownership and destination checks are
still derived by the existing one-pass assignment/store executor. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LoanSafeMachine.assign_packet_empty {before world : World} {active : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (uninitialized : world.memory[binding.address]? = some (.node .tuple 0 []))
    {rhs : Expr} {packet : ValueCell} {middle : State}
    (expression : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      Addressed.expression world active.roots (current.loans ++ suspended.reads) active.state rhs = some (packet, middle))
    (empty : middle slot = .empty) (safeMiddle : LoanSafeState middle) (safeValue : LoanSafe (Slot.ofValue packet.2)) :
    Derived.assign world active callers slot rhs = some (world.write binding.address packet.1,
      {active with state := middle.set slot (Slot.ofValue packet.2)}) ∧
    LoanSafeMachine before callers previous external (world.write binding.address packet.1)
      {active with state := middle.set slot (Slot.ofValue packet.2)} := by
  obtain ⟨current, scan, scanned⟩ := active.scan_complete h.valid
  obtain ⟨suspended, callerScan, callerView⟩ := scanCallers_complete callers h.callersValid
  have evaluated := expression current suspended scanned callerView
  obtain ⟨_, readable, remainingFrame⟩ := Addressed.expression_readable scanned.frame evaluated
  let mid : Activation := {active with state := middle}
  have valid : mid.Valid world := ⟨h.valid.1, _, remainingFrame⟩
  obtain ⟨remainder, remainingScan, inventory, _⟩ := mid.context_complete valid slot
  obtain ⟨owners, footprint, ownerFrame⟩ := Addressed.expression_owner_frame h.valid h.ownerFrame evaluated
  have roots := Derived.RootLoansAllowed.of_safe_preserved (slot := slot) (active := mid) safeMiddle
    uninitialized (Or.inl rfl) h.previousCallers h.beforeWellFormed h.kept (h.fresh slot binding hb)
  have payload := Derived.PacketLoansAvoid.of_safe (packet := packet) safeValue uninitialized (Or.inl rfl)
  have stored := Derived.store_complete valid h.wellFormed h.separate hb empty readable footprint ownerFrame inventory callerView
    (Derived.StoreLoansAllowed.of_parts roots payload)
  have run := Derived.assign_run scan callerScan evaluated remainingScan stored
  refine ⟨run, h.advance (act := .assign slot rhs) run (safeMiddle.set slot safeValue) h.separate ?_ h.fresh⟩
  simpa only [World.write, List.length_set] using h.memoryBound

theorem copy_shared_packet {world : World} {active : Activation} {slot : Nat} {binding : Binding} {pointer : Pointer} {value : Value}
    (hb : active.roots slot = some binding) (raw : world.memory[binding.address]? = some (.shared pointer))
    (initialized : active.state slot = .shared value) (blocked : List Nat) :
    Addressed.expression world active.roots blocked active.state (.use (.copy (.local slot))) =
      some ((.shared pointer, .reference value), active.state) := by
  simp only [Addressed.expression, Addressed.operand, Addressed.read, Partial.Locals.read, splitPlace, Slot.read, Slot.get,
    initialized, Slot.materialize, Storage.locate, hb, raw, locatePath, copyCell, bind, Option.bind]

theorem move_local_packet {world : World} {active : Activation} {slot : Nat} {binding : Binding} {cell : Cell} {value : Value}
    (hb : active.roots slot = some binding) (raw : world.memory[binding.address]? = some cell)
    (initialized : (active.state slot).materialize = some value) {blocked : List Nat} (allowed : binding.address ∉ blocked) :
    Addressed.operand world active.roots blocked active.state (.move (.local slot)) =
      some ((cell, value), active.state.set slot .empty) := by
  simp only [Addressed.operand, Partial.Locals.move, splitPlace, Slot.take, initialized,
    Storage.locate, hb, raw, locatePath, bind, Option.bind, allowed, ite_false]


theorem aggregate_two_packets {world : World} {active : Activation} {first second : Nat}
    {firstRoot secondRoot : Binding} {leftCell rightCell : Cell} {left right : Value} {blocked : List Nat}
    (firstBinding : active.roots first = some firstRoot) (secondBinding : active.roots second = some secondRoot)
    (firstRaw : world.memory[firstRoot.address]? = some leftCell) (secondRaw : world.memory[secondRoot.address]? = some rightCell)
    (firstValue : (active.state first).materialize = some left) (secondValue : (active.state second).materialize = some right)
    (different : second ≠ first) (firstAllowed : firstRoot.address ∉ blocked) (secondAllowed : secondRoot.address ∉ blocked)
    (kind : Kind) (tag : Nat) :
    Addressed.expression world active.roots blocked active.state (.aggregate kind tag [.move (.local first), .move (.local second)]) =
      some ((.node kind tag [leftCell, rightCell], .node kind tag [left, right]), (active.state.set first .empty).set second .empty) := by
  have firstRun := move_local_packet firstBinding firstRaw firstValue firstAllowed
  have value2 : ((active.state.set first .empty) second).materialize = some right := by
    simpa only [Partial.Locals.set, different, ite_false] using secondValue
  have secondRun := move_local_packet (active := {active with state := active.state.set first .empty}) secondBinding secondRaw value2 secondAllowed
  simp only [Addressed.expression, Addressed.operands, firstRun, secondRun, List.map_cons, List.map_nil, bind, Option.bind]

end SubtreeProofs.Rust.SourceEval.Addressed
