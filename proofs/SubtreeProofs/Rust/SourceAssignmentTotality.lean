module

public import SubtreeProofs.Rust.SourceReturnTotality
public import SubtreeProofs.Rust.SourceOwnerActions

/-! One-pass forward actual assignment. Independent source RHS success and
selected move/loan permissions construct addressed RHS execution and its store.
The post-RHS frame, packet ownership and remaining inventories are derived.
No successful assignment, desired final heap or post-store frame is supplied. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

def ExpressionLoansAvoid (world : World) (roots : Roots) (blocked : List Nat) (state : State)
    (rhs : Expr) (address : Nat) : Prop :=
  ∀ packet masks, Addressed.expression world roots blocked state rhs = some (packet, masks) →
    PacketLoansAvoid world packet address

theorem ExpressionLoansAvoid.of_closed {world : World} {roots : Roots} {frame : Nat} {state middle : State}
    {guards blocked : List Nat} (hf : Frame world frame roots state guards) {rhs : Expr} {value : Value}
    (source : SourceEval.expression state rhs = some (value, middle)) {ty : Ty}
    (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty) (address : Nat) :
    ExpressionLoansAvoid world roots blocked state rhs address := by
  intro packet masks run
  rcases packet with ⟨cell, actual⟩
  obtain ⟨_, execution, _, _, _⟩ := Addressed.expression_spec hf run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (source.symm.trans execution))
  exact PacketLoansAvoid.of_closed typed closed

theorem assign_complete {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle)) (empty : middle slot = .empty)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      Addressed.AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs)
    (roots : RootLoansAllowed world {active with state := middle} callers slot binding)
    (payload : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ExpressionLoansAvoid world active.roots (current.loans ++ suspended.reads) active.state rhs binding.address) :
    ∃ cell, assign world active callers slot rhs = some (world.write binding.address cell,
      {active with state := middle.set slot (Slot.ofValue value)}) := by
  obtain ⟨current, hs, scanned⟩ := active.scan_complete ha
  obtain ⟨suspended, ht, callerView⟩ := scanCallers_complete callers hc
  obtain ⟨cell, run⟩ := Addressed.expression_complete scanned.frame source (moves current suspended scanned callerView)
  obtain ⟨_, readable, remainingFrame⟩ := Addressed.expression_readable scanned.frame run
  have middleValid : ({active with state := middle} : Activation).Valid world := ⟨ha.1, _, remainingFrame⟩
  obtain ⟨remainder, hr, inventory, _⟩ := ({active with state := middle} : Activation).context_complete middleValid slot
  obtain ⟨owners, footprint, ownerFrame⟩ := Addressed.expression_owner_frame ha hf run
  have clear := payload current suspended scanned callerView (cell, value) middle run
  have stored := store_complete middleValid hw separate hb empty readable footprint ownerFrame inventory callerView
    (StoreLoansAllowed.of_parts roots clear)
  exact ⟨cell, assign_run hs ht run hr stored⟩

theorem assign_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle)) (empty : middle slot = .empty)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      Addressed.AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs)
    (roots : RootLoansAllowed world {active with state := middle} callers slot binding)
    (payload : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ExpressionLoansAvoid world active.roots (current.loans ++ suspended.reads) active.state rhs binding.address) :
    ∃ cell, assign world active callers slot rhs = some (world.write binding.address cell,
        {active with state := middle.set slot (Slot.ofValue value)}) ∧
      Step world active callers (.assign slot rhs) (world.write binding.address cell)
        {active with state := middle.set slot (Slot.ofValue value)} (Cost.local (Action.assign slot rhs).weight) ∧
      OwnerFrame (world.write binding.address cell)
        (({active with state := middle.set slot (Slot.ofValue value)} : Activation).owners (world.write binding.address cell) ++
          (callerOwners (world.write binding.address cell) callers ++ external)) ∧
      BoxCoverage (world.write binding.address cell)
        (({active with state := middle.set slot (Slot.ofValue value)} : Activation).owners (world.write binding.address cell) ++
          (callerOwners (world.write binding.address cell) callers ++ external)) := by
  obtain ⟨cell, run⟩ := assign_complete ha hc hw separate hf hb source empty moves roots payload
  have physical : action world active callers (.assign slot rhs) = some (world.write binding.address cell,
      {active with state := middle.set slot (Slot.ofValue value)}) := run
  have step := action_spec ha hc hw (.assign slot rhs) physical
  obtain ⟨_, _, _, frame, coverage⟩ := action_owner_resources ha hc hw (.assign slot rhs) hf covered physical
  exact ⟨cell, run, step, frame, coverage⟩

theorem assign_complete_closed {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle)) (empty : middle slot = .empty)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      Addressed.AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs)
    (roots : RootLoansAllowed world {active with state := middle} callers slot binding)
    {ty : Ty} (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty) :
    ∃ cell, assign world active callers slot rhs = some (world.write binding.address cell,
      {active with state := middle.set slot (Slot.ofValue value)}) := by
  apply assign_complete ha hc hw separate hf hb source empty moves roots
  intro current suspended scanned _
  exact ExpressionLoansAvoid.of_closed scanned.frame source typed closed binding.address

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
