module

public import SubtreeProofs.Rust.SourceScrutineeTotality
public import SubtreeProofs.Rust.SourceActivationLoanViews

/-! A forward invariant for closed, call-free sections of the actual machine.
Fresh stack roots and preserved caller inventories discharge local move guards.
Complete owner conservation retains permission to destroy transferred values.
The invariant allows arbitrary aliases among suspended shared reads. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def ClosedState (state : State) : Prop :=
  ∀ slot, ∃ ty, SlotTyped (state slot) ty ∧ Borrow.Closed ty

theorem ClosedState.set {state : State} (h : ClosedState state) (slot : Nat)
    {part : Slot} {ty : Ty} (typed : SlotTyped part ty) (closed : Borrow.Closed ty) :
    ClosedState (state.set slot part) := by
  intro index
  by_cases same : index = slot
  · subst index; exact ⟨ty, by simpa only [Partial.Locals.set, ite_true] using typed, closed⟩
  · simpa only [Partial.Locals.set, same, ite_false] using h index

theorem ClosedState.clear {state : State} (h : ClosedState state) (slot : Nat) :
    ClosedState (state.set slot .empty) :=
  h.set slot (SlotTyped.empty .u32) .u32

theorem ClosedState.forget {state : State} (h : ClosedState state) (code : Code) (slots : List Nat) :
    LoanEnding.forget code slots state = state := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    rw [LoanEnding.forget_cons]
    obtain ⟨ty, typed, closed⟩ := h slot
    have notShared : ∀ value, state slot ≠ .shared value := by
      intro value eq
      rw [eq] at typed
      cases typed
      cases closed
    cases hs : state slot <;> try exact ih
    exact False.elim (notShared _ hs)

theorem ClosedState.forgetRefs {active : Activation} (h : ClosedState active.state) (code : Code) :
    active.forgetRefs code = active := by
  unfold Activation.forgetRefs
  change ({active with state := LoanEnding.forget code (List.range active.count) active.state} : Activation) = active
  rw [h.forget]

namespace Derived

theorem action_owner_subset {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {act : Action} (run : action world active callers act = some (final, after)) :
    after.owners final ⊆ active.owners world := by
  obtain ⟨discarded, partition, _, finalFrame, _⟩ := action_owner_resources ha hc hw act hf covered run
  have step := action_spec ha hc hw act run
  obtain ⟨r, scanned, represented, _⟩ := step.suspended
  have same := (scanCallers_spec hc scanned).owners_preserved represented
  intro address member
  have old := partition.symm.subset (List.mem_append_right _ (List.mem_append_left _ member))
  rcases List.mem_append.mp old with owned | other
  · exact owned
  · rw [same] at other
    exact False.elim (List.disjoint_left.mp finalFrame.unique.disjoint member other)

end Derived

def LocalMoves : Operand → Prop
  | .move (.local _) => True
  | .move _ => False
  | _ => True

def LocalMovesExpr : Expr → Prop
  | .use op => LocalMoves op
  | .address _ => True
  | .aggregate _ _ ops => ∀ op ∈ ops, LocalMoves op
  | .less left right => LocalMoves left ∧ LocalMoves right

structure ClosedMachine (before : World) (callers : List Activation) (previous : Resources)
    (external : List Nat) (world : World) (active : Activation) : Prop where
  beforeWellFormed : before.WellFormed
  previousCallers : Callers before callers previous
  kept : Preserves before world previous.reads
  valid : active.Valid world
  wellFormed : world.WellFormed
  separate : active.RootsSeparate callers
  memoryBound : before.memory.length ≤ world.memory.length
  fresh : ∀ slot binding, active.roots slot = some binding → before.memory.length ≤ binding.address
  closed : ClosedState active.state
  ownerFrame : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external))
  coverage : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external))
  ownersAvoid : List.Disjoint (active.owners world) previous.loans

namespace ClosedMachine

variable {before world : World} {callers : List Activation} {previous : Resources}
  {external : List Nat} {active : Activation}

theorem callersValid (h : ClosedMachine before callers previous external world active) :
    ∀ caller ∈ callers, caller.Valid world := by
  intro caller member
  obtain ⟨_, scanned, _, _, _⟩ := (h.previousCallers.transport h.kept).get member
  exact scanned.valid

theorem rootLoans (h : ClosedMachine before callers previous external world active)
    {middle : State} (typed : ClosedState middle) {slot : Nat} {binding : Binding}
    (hb : active.roots slot = some binding) :
    Derived.RootLoansAllowed world {active with state := middle} callers slot binding :=
  Derived.RootLoansAllowed.of_closed_preserved (fun index _ => typed index)
    h.previousCallers h.beforeWellFormed h.kept (h.fresh slot binding hb)

theorem moveLocal (h : ClosedMachine before callers previous external world active)
    {current suspended : Resources} (scan : Scanned world active current) (view : Callers world callers suspended)
    (slot : Nat) : Allowed world active.roots (current.loans ++ suspended.reads) (.move (.local slot)) := by
  have noLoans := scan.inventory.closed_loans (fun index _ => h.closed index)
  intro cell pointer located
  cases hb : active.roots slot with
  | none => simp only [Storage.locate, splitPlace, hb, bind, Option.bind, reduceCtorEq] at located
  | some binding =>
    apply allowed_local_from_loans h.valid h.separate h.ownerFrame view hb ?_ cell pointer located
    rw [noLoans, List.nil_append]
    intro borrowed
    have bound := h.previousCallers.preserved_read_bound h.beforeWellFormed h.kept view binding.address
      (view.loans_subset_reads borrowed)
    have fresh := h.fresh slot binding hb
    omega

theorem moves (h : ClosedMachine before callers previous external world active)
    {current suspended : Resources} (scan : Scanned world active current) (view : Callers world callers suspended)
    {op : Operand} (restricted : LocalMoves op) :
    Allowed world active.roots (current.loans ++ suspended.reads) op := by
  cases op with
  | move place => cases place with
    | «local» slot => exact h.moveLocal scan view slot
    | field _ _ _ | deref _ => cases restricted
  | copy _ | number _ | boolean _ => trivial

theorem expressions (h : ClosedMachine before callers previous external world active)
    {current suspended : Resources} (scan : Scanned world active current) (view : Callers world callers suspended)
    {rhs : Expr} (restricted : LocalMovesExpr rhs) :
    AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs := by
  cases rhs with
  | use op => exact h.moves scan view restricted
  | address _ => trivial
  | aggregate _ _ ops => exact fun op member => h.moves scan view (restricted op member)
  | less left right => exact ⟨h.moves scan view restricted.1, h.moves scan view restricted.2⟩

theorem dropLoans (h : ClosedMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) :
    Derived.DropLoansAllowed world active callers slot binding := by
  apply Derived.DropLoansAllowed.of_closed_preserved (fun index _ => h.closed index)
    h.previousCallers h.beforeWellFormed h.kept (h.fresh slot binding hb)
  intro item represented
  have bound : slot < active.count := by
    by_contra no
    have impossible := h.valid.1 slot (by omega)
    rw [hb] at impossible
    cases impossible
  have partition := active.owners_partition world slot bound represented.source.ownerList
  exact List.disjoint_left.mpr (fun address owned borrowed =>
    List.disjoint_left.mp h.ownersAvoid
      (partition.symm.subset (List.mem_append_left _ owned)) borrowed)

theorem advance (h : ClosedMachine before callers previous external world active)
    {final : World} {after : Activation} {act : Action}
    (run : Derived.action world active callers act = some (final, after))
    (closed : ClosedState after.state) (separate : after.RootsSeparate callers)
    (memoryBound : before.memory.length ≤ final.memory.length)
    (fresh : ∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) :
    ClosedMachine before callers previous external final after := by
  have step := Derived.action_spec h.valid h.callersValid h.wellFormed act run
  obtain ⟨r, scanned, _, kept⟩ := step.suspended
  have same := (scanCallers_spec h.callersValid scanned).unique (h.previousCallers.transport h.kept)
  rw [same] at kept
  obtain ⟨_, _, _, frame, coverage⟩ :=
    Derived.action_owner_resources h.valid h.callersValid h.wellFormed act h.ownerFrame h.coverage run
  refine ⟨h.beforeWellFormed, h.previousCallers, h.kept.trans kept, step.valid, step.wellFormed,
    separate, memoryBound, fresh, closed, frame, coverage, ?_⟩
  have subset := Derived.action_owner_subset h.valid h.callersValid h.wellFormed h.ownerFrame h.coverage run
  exact List.disjoint_left.mpr (fun address owned => List.disjoint_left.mp h.ownersAvoid (subset owned))

theorem storageLive (h : ClosedMachine before callers previous external world active) {slot : Nat}
    (bound : slot < active.count) (unbound : active.roots slot = none) :
    let final := world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])
    let after : Activation := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty}
    Derived.storageLive world active callers slot = some (final, after) ∧
      ClosedMachine before callers previous external final after := by
  dsimp only
  have run := Derived.storageLive_complete h.valid h.callersValid bound unbound
  refine ⟨run, h.advance (act := .storageLive slot) run (h.closed.clear slot) (h.separate.set_fresh h.callersValid slot _ (Nat.le_refl _)) ?_ ?_⟩
  · have length := (world.allocate_spec (.stack active.frame slot world.memory.length) (.node .tuple 0 [])).2.2.2.2
    rw [length]
    exact h.memoryBound.trans (by omega)
  · intro index binding hb
    by_cases same : index = slot
    · subst index
      simp only [Roots.set, ite_true, Option.some.injEq] at hb
      cases hb
      exact h.memoryBound
    · exact h.fresh index binding (by simpa only [Roots.set, same, ite_false] using hb)

theorem storageDead (h : ClosedMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (zero : (active.state slot).dropWork.boxes = 0) :
    let final := world.retire [binding.address]
    let after : Activation := {active with roots := active.roots.set slot none, state := active.state.set slot .empty}
    Derived.storageDead world active callers slot = some (final, after) ∧
      ClosedMachine before callers previous external final after := by
  dsimp only
  have run := Derived.storageDead_complete h.valid h.callersValid h.wellFormed h.separate h.ownerFrame hb zero
    (h.rootLoans h.closed hb)
  refine ⟨run, h.advance (act := .storageDead slot) run (h.closed.clear slot) (h.separate.erase slot) h.memoryBound ?_⟩
  intro index binding hr
  by_cases same : index = slot
  · subst index; simp only [Roots.set, ite_true, reduceCtorEq] at hr
  · exact h.fresh index binding (by simpa only [Roots.set, same, ite_false] using hr)

theorem assign (h : ClosedMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle))
    (empty : middle slot = .empty) (restricted : LocalMovesExpr rhs) (closedMiddle : ClosedState middle)
    {ty : Ty} (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty) :
    ∃ cell, Derived.assign world active callers slot rhs = some (world.write binding.address cell,
        {active with state := middle.set slot (Slot.ofValue value)}) ∧
      ClosedMachine before callers previous external (world.write binding.address cell)
        {active with state := middle.set slot (Slot.ofValue value)} := by
  obtain ⟨cell, run⟩ := Derived.assign_complete_closed h.valid h.callersValid h.wellFormed h.separate h.ownerFrame hb
    source empty (fun _ _ scan view => h.expressions scan view restricted) (h.rootLoans closedMiddle hb) typed closed
  refine ⟨cell, run, h.advance (act := .assign slot rhs) run (closedMiddle.set slot (ofValue_typed typed) closed) h.separate ?_ h.fresh⟩
  simpa only [World.write, List.length_set] using h.memoryBound

theorem drop (h : ClosedMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding) :
    ∃ discarded, Derived.drop world active callers slot = some (world.retire discarded,
        {active with state := active.state.set slot .empty}) ∧
      ClosedMachine before callers previous external (world.retire discarded)
        {active with state := active.state.set slot .empty} ∧
      discarded.length = (active.state slot).dropWork.boxes := by
  obtain ⟨discarded, run, _, length⟩ := Derived.drop_complete h.valid h.callersValid h.separate h.ownerFrame hb (h.dropLoans hb)
  exact ⟨discarded, run, h.advance (act := .drop slot) run (h.closed.clear slot) h.separate h.memoryBound h.fresh, length⟩

theorem switchBool (h : ClosedMachine before callers previous external world active)
    {slot : Nat} {value : Bool} (initialized : active.state slot = .boolean value) :
    Derived.scrutinee world active callers (.value (.move slot)) =
        some (.boolean value, {active with state := active.state.set slot .empty}) ∧
      ClosedMachine before callers previous external world {active with state := active.state.set slot .empty} := by
  have source : SourceEval.scrutinee active.state (.value (.move slot)) =
      some (.boolean value, active.state.set slot .empty) := by
    simp only [SourceEval.scrutinee, SourceEval.operand, Partial.Locals.move, splitPlace, initialized,
      Slot.take, Slot.materialize, bind, Option.bind]
  obtain ⟨run, valid, frame, coverage⟩ := Derived.scrutinee_total h.valid h.callersValid (.value (.move slot))
    h.ownerFrame h.coverage source (fun _ _ scan view => h.moveLocal scan view slot)
  refine ⟨run, h.beforeWellFormed, h.previousCallers, h.kept, valid, h.wellFormed, h.separate,
    h.memoryBound, h.fresh, h.closed.clear slot, frame, coverage, ?_⟩
  apply List.disjoint_left.mpr
  intro address member borrowed
  have old := h.coverage address (frame.classified address (List.mem_append_left _ member))
    (frame.alive address (List.mem_append_left _ member))
  rcases List.mem_append.mp old with owner | other
  · exact List.disjoint_left.mp h.ownersAvoid owner borrowed
  · exact List.disjoint_left.mp frame.unique.disjoint member other

end ClosedMachine

namespace Calling

theorem exec_noncall_step {callee : Derived.Callees} {callers : List Activation}
    {world middle : World} {active current : Activation} {act : Action} {rest : Code}
    (closed : ClosedState active.state) (run : Derived.action world active callers act = some (middle, current))
    {flow : Derived.Flow} {last : Cost} (tail : exec callee callers rest middle current = some (flow, last)) :
    exec callee callers (.step act rest) world active =
      some (flow, (Derived.actionCost active act).plus last) := by
  rw [exec_step, closed.forgetRefs]
  have first : instruction callee callers (world, active) act =
      some ((middle, current), Derived.actionCost active act) := by
    cases act with
    | call _ _ _ | undefinedBehavior => cases run
    | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ =>
      all_goals change (do let (next, after) ← Derived.action world active callers _; some ((next, after), _)) = _
      all_goals rw [run]; rfl
  simp only [first, tail, bind, Option.bind]

end Calling

inductive ClosedSteps (callers : List Activation) : World → Activation → List Action → World → Activation → Prop where
  | nil (world : World) (active : Activation) : ClosedSteps callers world active [] world active
  | cons {world middle final : World} {active current after : Activation} {act : Action} {rest : List Action} :
      ClosedState active.state → Derived.action world active callers act = some (middle, current) →
      ClosedSteps callers middle current rest final after →
      ClosedSteps callers world active (act :: rest) final after

theorem ClosedSteps.exec {callers : List Activation} {world final : World} {active after : Activation} {actions : List Action}
    (h : ClosedSteps callers world active actions final after) (callee : Derived.Callees) {rest : Code}
    {flow : Derived.Flow} {cost : Cost} (tail : Calling.exec callee callers rest final after = some (flow, cost)) :
    ∃ total, Calling.exec callee callers (actions.foldr Control.Tree.step rest) world active = some (flow, total) := by
  induction h with
  | nil => exact ⟨cost, tail⟩
  | cons closed step _ ih =>
    obtain ⟨work, hr⟩ := ih tail
    exact ⟨_, Calling.exec_noncall_step closed step hr⟩

end SubtreeProofs.Rust.SourceEval.Addressed
