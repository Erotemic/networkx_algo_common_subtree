module

public import SubtreeProofs.Rust.SourceQueryMachine

/-! Forward machines whose finitely designated reference locals borrow only
pre-entry data. This covers original queries and tuples of copied queries;
closed owned locals remain unrestricted and may own the borrowed data. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem Inventory.loans_below_family {world : World} {active : Activation} {limit : Nat}
    {slots exceptions : List Nat} {r : Resources}
    (h : Inventory world active.frame active.roots active.state slots r)
    (closed : ClosedOutside exceptions active.state)
    (origins : ∀ slot ∈ exceptions, LoanOrigin world active limit slot) :
    ∀ address ∈ r.loans, address < limit := by
  induction h with
  | nil => simp
  | @cons slot slots head tail represented rest ih =>
    have headBound : ∀ address ∈ head.loans, address < limit := by
      by_cases member : slot ∈ exceptions
      · exact (origins slot member).bound represented
      · obtain ⟨ty, typed, shape⟩ := closed slot member
        rw [represented.closed_loans typed shape]
        simp
    intro address member
    rcases List.mem_append.mp member with first | remaining
    · exact headBound address first
    · exact ih address remaining

structure OriginalLoanMachine (before : World) (callers : List Activation) (previous : Resources)
    (external exceptions : List Nat) (world : World) (active : Activation) : Prop where
  native : LoanSafeMachine before callers previous external world active
  closed : ClosedOutside exceptions active.state
  zero : ∀ slot ∈ exceptions, (active.state slot).dropWork.boxes = 0
  origins : ∀ slot ∈ exceptions, LoanOrigin world active before.memory.length slot

namespace OriginalLoanMachine

variable {before world : World} {active : Activation} {callers : List Activation}
  {previous : Resources} {external exceptions : List Nat}

theorem prepare (h : OriginalLoanMachine before callers previous external exceptions world active) (code : Code) :
    OriginalLoanMachine before callers previous external exceptions world (active.forgetRefs code) := by
  refine ⟨h.native.prepare code, h.closed.forget code _, ?_, fun slot member => (h.origins slot member).prepare code⟩
  intro slot member
  rcases LoanEnding.forget_eq_or_empty code (List.range active.count) active.state slot with same | empty
  · change (LoanEnding.forget code _ active.state slot).dropWork.boxes = 0
    rw [same]; exact h.zero slot member
  · change (LoanEnding.forget code _ active.state slot).dropWork.boxes = 0
    rw [empty]; simp only [Slot.dropWork]

theorem prepare_closed_local (h : OriginalLoanMachine before callers previous external exceptions world active)
    (code : Code) (slot : Nat) (outside : slot ∉ exceptions) : (active.forgetRefs code).state slot = active.state slot := by
  obtain ⟨ty, typed, closed⟩ := h.closed slot outside
  exact LoanEnding.forget_closed code _ typed closed

theorem moves (h : OriginalLoanMachine before callers previous external exceptions world active)
    {current suspended : Resources} (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {op : Operand} (inlineOp : InlineOperand op) : Allowed world active.roots (current.loans ++ suspended.reads) op := by
  cases op with
  | copy _ | number _ | boolean _ => trivial
  | move place =>
    intro cell pointer located forbidden
    obtain ⟨binding, hb, same⟩ := locate_inline_root inlineOp located
    have fresh := h.native.fresh _ binding hb
    rw [same] at forbidden
    rcases List.mem_append.mp forbidden with currentLoan | oldRead
    · have bound := Inventory.loans_below_family scanned.inventory h.closed h.origins binding.address currentLoan
      omega
    · have bound := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed h.native.kept callerView binding.address oldRead
      omega

theorem expressions (h : OriginalLoanMachine before callers previous external exceptions world active)
    {current suspended : Resources} (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {rhs : Expr} (inlineExpr : InlineExpr rhs) : AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs := by
  cases rhs with
  | use op => exact h.moves scanned callerView inlineExpr
  | address _ => trivial
  | aggregate _ _ ops => exact fun op member => h.moves scanned callerView (inlineExpr op member)
  | less left right => exact ⟨h.moves scanned callerView inlineExpr.1, h.moves scanned callerView inlineExpr.2⟩

theorem rootLoans (h : OriginalLoanMachine before callers previous external exceptions world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) : Derived.RootLoansAllowed world active callers slot binding := by
  intro remainder suspended remaining callerView forbidden
  have fresh := h.native.fresh slot binding hb
  rcases List.mem_append.mp forbidden with current | old
  · have bound := Inventory.loans_below_family remaining h.closed h.origins binding.address current
    omega
  · have bound := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed h.native.kept callerView
      binding.address (callerView.loans_subset_reads old)
    omega

theorem safe_middle (h : OriginalLoanMachine before callers previous external exceptions world active) {middle : State}
    (closed : ClosedOutside exceptions middle) (same : ∀ slot ∈ exceptions, middle slot = active.state slot) : LoanSafeState middle := by
  intro slot
  by_cases member : slot ∈ exceptions
  · rw [same slot member]; exact h.native.safe slot
  · obtain ⟨ty, typed, shape⟩ := closed slot member
    exact LoanSafe.of_closed typed shape

theorem storageLive (h : OriginalLoanMachine before callers previous external exceptions world active)
    {slot : Nat} (bound : slot < active.count) (unbound : active.roots slot = none) (other : slot ∉ exceptions) :
    let final := world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])
    let after : Activation := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty}
    Derived.storageLive world active callers slot = some (final, after) ∧
      OriginalLoanMachine before callers previous external exceptions final after := by
  obtain ⟨run, native⟩ := h.native.storageLive bound unbound
  refine ⟨run, native, h.closed.clear slot, ?_, ?_⟩
  · intro index member
    have different : index ≠ slot := by intro same; subst index; exact other member
    simpa only [Partial.Locals.set, different, ite_false] using h.zero index member
  · intro index member
    have different : index ≠ slot := by intro same; subst index; exact other member
    exact ((h.origins index member).allocate h.native.wellFormed _ _).congr
      (after := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty})
      rfl (by simp only [Roots.set, different, ite_false]) (by simp only [Partial.Locals.set, different, ite_false])

theorem assign_empty (h : OriginalLoanMachine before callers previous external exceptions world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) (other : slot ∉ exceptions)
    (uninitialized : world.memory[binding.address]? = some (.node .tuple 0 []))
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle)) (empty : middle slot = .empty)
    (closedMiddle : ClosedOutside exceptions middle) (same : ∀ index ∈ exceptions, middle index = active.state index)
    (inlineExpr : InlineExpr rhs) {ty : Ty} (typed : SnapshotTyped value ty) (closedValue : Borrow.Closed ty) :
    ∃ cell, Derived.assign world active callers slot rhs = some (world.write binding.address cell,
        {active with state := middle.set slot (Slot.ofValue value)}) ∧
      OriginalLoanMachine before callers previous external exceptions (world.write binding.address cell)
        {active with state := middle.set slot (Slot.ofValue value)} := by
  obtain ⟨cell, run, native⟩ := h.native.assign_empty hb uninitialized source empty (h.safe_middle closedMiddle same)
    (LoanSafe.of_closed (ofValue_typed typed) closedValue) (fun _ _ scanned callerView => h.expressions scanned callerView inlineExpr)
  have masks : ∀ index ∈ exceptions, (middle.set slot (Slot.ofValue value)) index = active.state index := by
    intro index member
    have different : index ≠ slot := by intro eq; subst index; exact other member
    simpa only [Partial.Locals.set, different, ite_false] using same index member
  refine ⟨cell, run, native, closedMiddle.set slot (ofValue_typed typed) closedValue, ?_, ?_⟩
  · intro index member
    change ((middle.set slot (Slot.ofValue value)) index).dropWork.boxes = 0
    rw [masks index member]; exact h.zero index member
  · intro index member
    have different : index ≠ slot := by intro eq; subst index; exact other member
    exact ((h.origins index member).write_other h.native.valid hb different (h.zero index member) (h.native.fresh slot binding hb) cell).congr
      (after := {active with state := middle.set slot (Slot.ofValue value)}) rfl rfl (masks index member)

theorem storageDead (h : OriginalLoanMachine before callers previous external exceptions world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) (zero : (active.state slot).dropWork.boxes = 0) :
    let final := world.retire [binding.address]
    let after : Activation := {active with roots := active.roots.set slot none, state := active.state.set slot .empty}
    Derived.storageDead world active callers slot = some (final, after) ∧
      OriginalLoanMachine before callers previous external exceptions final after := by
  dsimp only
  have run := Derived.storageDead_complete h.native.valid h.native.callersValid h.native.wellFormed
    h.native.separate h.native.ownerFrame hb zero (h.rootLoans hb)
  have fresh : ∀ index target, (active.roots.set slot none) index = some target → before.memory.length ≤ target.address := by
    intro index target root
    by_cases same : index = slot
    · subst index; simp only [Roots.set, ite_true, reduceCtorEq] at root
    · exact h.native.fresh index target (by simpa only [Roots.set, same, ite_false] using root)
  have native := h.native.advance (act := .storageDead slot) run (h.native.safe.clear slot) (h.native.separate.erase slot) h.native.memoryBound fresh
  refine ⟨run, native, h.closed.clear slot, ?_, ?_⟩
  · intro index member
    by_cases same : index = slot
    · subst index; simp only [Partial.Locals.set, ite_true, Slot.dropWork]
    · simpa only [Partial.Locals.set, same, ite_false] using h.zero index member
  · intro index member
    by_cases same : index = slot
    · subst index
      exact LoanOrigin.of_closed native.valid before.memory.length slot
        (by simpa only [Partial.Locals.set, ite_true] using (SlotTyped.empty .u32)) .u32
    · exact ((h.origins index member).retire_other h.native.valid hb same (h.zero index member) (h.native.fresh slot binding hb)).congr
        (after := {active with roots := active.roots.set slot none, state := active.state.set slot .empty}) rfl
        (by simp only [Roots.set, same, ite_false]) (by simp only [Partial.Locals.set, same, ite_false])

theorem drop_zero (h : OriginalLoanMachine before callers previous external exceptions world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) (zero : (active.state slot).dropWork.boxes = 0) :
    Derived.drop world active callers slot = some (world, {active with state := active.state.set slot .empty}) ∧
      OriginalLoanMachine before callers previous external exceptions world {active with state := active.state.set slot .empty} := by
  have loans : Derived.DropLoansAllowed world active callers slot binding := by
    intro item remainder suspended represented remaining callerView
    have none : item.owners = [] := List.length_eq_zero_iff.mp (represented.boxes.trans zero)
    rw [none]
    apply List.disjoint_left.mpr
    intro address member forbidden
    have same : address = binding.address := List.mem_singleton.mp member
    subst address
    exact h.rootLoans hb remainder suspended remaining callerView forbidden
  obtain ⟨discarded, run, _, length⟩ := Derived.drop_complete h.native.valid h.native.callersValid h.native.separate h.native.ownerFrame hb loans
  have none : discarded = [] := List.length_eq_zero_iff.mp (length.trans zero)
  subst discarded
  have unchanged : world.retire [] = world := by
    cases world with
    | mk memory classes live =>
      have sameLive : SubtreeProofs.Rust.LookupSource.Partial.Addressed.retire live [] = live := by
        funext address
        exact SubtreeProofs.Rust.LookupSource.Partial.Addressed.retire_other live (by simp)
      simp only [World.retire, sameLive]
  rw [unchanged] at run
  have native := h.native.advance (act := .drop slot) run (h.native.safe.clear slot) h.native.separate h.native.memoryBound h.native.fresh
  refine ⟨run, native, h.closed.clear slot, ?_, ?_⟩
  · intro index member
    by_cases same : index = slot
    · subst index; simp only [Partial.Locals.set, ite_true, Slot.dropWork]
    · simpa only [Partial.Locals.set, same, ite_false] using h.zero index member
  · intro index member
    by_cases same : index = slot
    · subst index; exact (h.origins slot member).clear
    · exact (h.origins index member).congr
        (after := {active with state := active.state.set slot .empty}) rfl rfl
        (by simp only [Partial.Locals.set, same, ite_false])

end OriginalLoanMachine
end SubtreeProofs.Rust.SourceEval.Addressed
