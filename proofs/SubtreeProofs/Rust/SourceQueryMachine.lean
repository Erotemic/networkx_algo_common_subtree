module

public import SubtreeProofs.Rust.SourceInlineMovePermissions
public import SubtreeProofs.Rust.SourceEvaluatorClosedLocals

/-! Forward native machines with only the original query locals containing
references. Their bounded read origins discharge selected fresh stack-root
permissions while table/query/actual-caller shared aliases remain permitted. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LoanEnding

open LookupSource Partial

theorem forget_unshared (code : Code) (slots : List Nat) {state : State} {index : Nat}
    (unshared : ∀ value, state index ≠ .shared value) : forget code slots state index = state index := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    rw [forget_cons]
    cases shared : state slot <;> try exact ih unshared
    have different : index ≠ slot := by intro same; subst index; exact unshared _ shared
    by_cases ended : endsBeforeObservation slot code = true
    · simp only [ended, ite_true]
      have safe : ∀ value, (state.set slot .empty) index ≠ .shared value := by
        simpa only [Partial.Locals.set, different, ite_false] using unshared
      simpa only [Partial.Locals.set, different, ite_false] using ih safe
    · simpa only [ended, Bool.false_eq_true, ite_false] using ih unshared

theorem forget_closed (code : Code) (slots : List Nat) {state : State} {index : Nat} {ty : Heap.Ty}
    (typed : Partial.SlotTyped (state index) ty) (closed : Heap.Borrow.Closed ty) :
    forget code slots state index = state index := by
  apply forget_unshared code slots
  intro value same
  rw [same] at typed
  cases typed
  cases closed

end SubtreeProofs.Rust.SourceEval.LoanEnding

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

structure QueryMachine (before : World) (callers : List Activation) (previous : Resources)
    (external : List Nat) (world : World) (active : Activation) : Prop where
  native : LoanSafeMachine before callers previous external world active
  closed : ClosedOutside [1, 2] active.state
  references : ReferenceQueries active.state
  origins : QueryOrigins world active before.memory.length

namespace QueryMachine

variable {before world : World} {active : Activation} {callers : List Activation} {previous : Resources} {external : List Nat}

theorem prepare (h : QueryMachine before callers previous external world active) (code : Code) :
    QueryMachine before callers previous external world (active.forgetRefs code) :=
  ⟨h.native.prepare code, h.closed.forget code _, h.references.prepare code _, h.origins.prepare code⟩

theorem prepare_closed_local (h : QueryMachine before callers previous external world active)
    (code : Code) (slot : Nat) (outside : slot ∉ [1, 2]) :
    (active.forgetRefs code).state slot = active.state slot := by
  obtain ⟨ty, typed, closed⟩ := h.closed slot outside
  exact LoanEnding.forget_closed code _ typed closed

theorem moves (h : QueryMachine before callers previous external world active)
    {current suspended : Resources} (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {op : Operand} (inlineOp : InlineOperand op) : Allowed world active.roots (current.loans ++ suspended.reads) op :=
  allowed_inline_from_query_origins h.native h.closed h.origins scanned callerView inlineOp

theorem expressions (h : QueryMachine before callers previous external world active)
    {current suspended : Resources} (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {rhs : Expr} (inlineExpr : InlineExpr rhs) : AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs := by
  cases rhs with
  | use op => exact h.moves scanned callerView inlineExpr
  | address _ => trivial
  | aggregate _ _ ops => exact fun op member => h.moves scanned callerView (inlineExpr op member)
  | less left right => exact ⟨h.moves scanned callerView inlineExpr.1, h.moves scanned callerView inlineExpr.2⟩

theorem rootLoans (h : QueryMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) :
    Derived.RootLoansAllowed world active callers slot binding := by
  intro remainder suspended remaining callerView forbidden
  have fresh := h.native.fresh slot binding hb
  rcases List.mem_append.mp forbidden with current | old
  · have bound := Inventory.loans_below_queries remaining h.closed h.origins binding.address current
    omega
  · have bound := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed h.native.kept callerView
      binding.address (callerView.loans_subset_reads old)
    omega

theorem safe_middle (h : QueryMachine before callers previous external world active) {middle : State}
    (closed : ClosedOutside [1, 2] middle) (queries : ∀ slot ∈ [1, 2], middle slot = active.state slot) : LoanSafeState middle := by
  intro slot
  by_cases member : slot ∈ [1, 2]
  · rw [queries slot member]; exact h.native.safe slot
  · obtain ⟨ty, typed, shape⟩ := closed slot member
    exact LoanSafe.of_closed typed shape

theorem storageLive (h : QueryMachine before callers previous external world active)
    {slot : Nat} (bound : slot < active.count) (unbound : active.roots slot = none) (other : slot ∉ [1, 2]) :
    let final := world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])
    let after : Activation := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty}
    Derived.storageLive world active callers slot = some (final, after) ∧ QueryMachine before callers previous external final after := by
  obtain ⟨run, native⟩ := h.native.storageLive bound unbound
  exact ⟨run, native, h.closed.clear slot, h.references.set_other slot other .empty,
    h.origins.allocate h.native.wellFormed slot other⟩

theorem assign_empty (h : QueryMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) (other : slot ∉ [1, 2])
    (uninitialized : world.memory[binding.address]? = some (.node .tuple 0 []))
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle)) (empty : middle slot = .empty)
    (closedMiddle : ClosedOutside [1, 2] middle) (queries : ∀ index ∈ [1, 2], middle index = active.state index)
    (inlineExpr : InlineExpr rhs) {ty : Ty} (typed : SnapshotTyped value ty) (closedValue : Borrow.Closed ty) :
    ∃ cell, Derived.assign world active callers slot rhs = some (world.write binding.address cell,
        {active with state := middle.set slot (Slot.ofValue value)}) ∧
      QueryMachine before callers previous external (world.write binding.address cell)
        {active with state := middle.set slot (Slot.ofValue value)} := by
  obtain ⟨cell, run, native⟩ := h.native.assign_empty hb uninitialized source empty (h.safe_middle closedMiddle queries)
    (LoanSafe.of_closed (ofValue_typed typed) closedValue) (fun _ _ scanned callerView => h.expressions scanned callerView inlineExpr)
  have masks : ∀ index ∈ [1, 2], (middle.set slot (Slot.ofValue value)) index = active.state index := by
    intro index member
    have different : index ≠ slot := by intro same; subst index; exact other member
    simpa only [Partial.Locals.set, different, ite_false] using queries index member
  have refs : ReferenceQueries (middle.set slot (Slot.ofValue value)) := by
    intro index member
    rw [masks index member]
    exact h.references index member
  have origins := (h.origins.write_other h.native.valid h.references hb other (h.native.fresh slot binding hb) cell).congr
    (after := {active with state := middle.set slot (Slot.ofValue value)}) rfl (fun _ _ => rfl) masks
  exact ⟨cell, run, native, closedMiddle.set slot (ofValue_typed typed) closedValue, refs, origins⟩

theorem storageDead (h : QueryMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (zero : (active.state slot).dropWork.boxes = 0) :
    let final := world.retire [binding.address]
    let after : Activation := {active with roots := active.roots.set slot none, state := active.state.set slot .empty}
    Derived.storageDead world active callers slot = some (final, after) ∧ QueryMachine before callers previous external final after := by
  dsimp only
  have run := Derived.storageDead_complete h.native.valid h.native.callersValid h.native.wellFormed
    h.native.separate h.native.ownerFrame hb zero (h.rootLoans hb)
  have fresh : ∀ index target, (active.roots.set slot none) index = some target → before.memory.length ≤ target.address := by
    intro index target root
    by_cases same : index = slot
    · subst index; simp only [Roots.set, ite_true, reduceCtorEq] at root
    · exact h.native.fresh index target (by simpa only [Roots.set, same, ite_false] using root)
  have native := h.native.advance (act := .storageDead slot) run (h.native.safe.clear slot)
    (h.native.separate.erase slot) h.native.memoryBound fresh
  refine ⟨run, native, h.closed.clear slot, h.references.clear slot, ?_⟩
  intro index member
  by_cases same : index = slot
  · subst index
    exact LoanOrigin.of_closed native.valid before.memory.length slot
      (by simpa only [Partial.Locals.set, ite_true] using (SlotTyped.empty .u32)) .u32
  · exact ((h.origins index member).retire_other h.native.valid hb same (h.references.boxes member)
      (h.native.fresh slot binding hb)).congr
      (after := {active with roots := active.roots.set slot none, state := active.state.set slot .empty}) rfl
      (by simp only [Roots.set, same, ite_false]) (by simp only [Partial.Locals.set, same, ite_false])

theorem drop_zero (h : QueryMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (zero : (active.state slot).dropWork.boxes = 0) :
    Derived.drop world active callers slot = some (world, {active with state := active.state.set slot .empty}) ∧
      QueryMachine before callers previous external world {active with state := active.state.set slot .empty} := by
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
  have native := h.native.advance (act := .drop slot) run (h.native.safe.clear slot)
    h.native.separate h.native.memoryBound h.native.fresh
  exact ⟨run, native, h.closed.clear slot, h.references.clear slot, h.origins.clear slot⟩

theorem closed_prepared (h : QueryMachine before callers previous external world active) (code : Code)
    (bound : ∀ slot ∈ [1, 2], slot < active.count)
    (ended : ∀ slot ∈ [1, 2], LoanEnding.endsBeforeObservation slot code = true) :
    ClosedState (active.forgetRefs code).state := by
  intro slot
  by_cases member : slot ∈ [1, 2]
  · have empty : (active.forgetRefs code).state slot = .empty := by
      rcases h.references slot member with empty | ⟨value, shared⟩
      · exact LoanEnding.forget_empty code _ empty
      · exact LoanEnding.forget_ended_shared code _ (List.mem_range.mpr (bound slot member)) shared (ended slot member)
    exact ⟨.u32, by rw [empty]; exact .empty _, .u32⟩
  · exact (h.closed.forget code _) slot member

end QueryMachine
end SubtreeProofs.Rust.SourceEval.Addressed
