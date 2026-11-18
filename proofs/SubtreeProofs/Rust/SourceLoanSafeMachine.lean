module

public import SubtreeProofs.Rust.SourceNativeLoanPermissions
public import SubtreeProofs.Rust.SourceClosedMachine

/-! Forward actual machines with native shared referents. Unlike closed local
states, these include the evaluator's table/query views and their allowed
aliases. Fresh stack bounds separate older actual callers; semantic graph
structure discharges fresh empty writes and reference-local move permissions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

structure LoanSafeMachine (before : World) (callers : List Activation) (previous : Resources)
    (external : List Nat) (world : World) (active : Activation) : Prop where
  beforeWellFormed : before.WellFormed
  previousCallers : Callers before callers previous
  kept : Preserves before world previous.reads
  valid : active.Valid world
  wellFormed : world.WellFormed
  separate : active.RootsSeparate callers
  memoryBound : before.memory.length ≤ world.memory.length
  fresh : ∀ slot binding, active.roots slot = some binding → before.memory.length ≤ binding.address
  safe : LoanSafeState active.state
  ownerFrame : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external))
  coverage : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external))

namespace LoanSafeMachine

variable {before world : World} {callers : List Activation} {previous : Resources}
  {external : List Nat} {active : Activation}

theorem callersValid (h : LoanSafeMachine before callers previous external world active) :
    ∀ caller ∈ callers, caller.Valid world := by
  intro caller member
  obtain ⟨_, scanned, _, _, _⟩ := (h.previousCallers.transport h.kept).get member
  exact scanned.valid

theorem prepare (h : LoanSafeMachine before callers previous external world active) (code : Code) :
    LoanSafeMachine before callers previous external world (active.forgetRefs code) := by
  refine ⟨h.beforeWellFormed, h.previousCallers, h.kept, Activation.forgetRefs_valid h.valid code,
    h.wellFormed, h.separate, h.memoryBound, h.fresh, h.safe.forget code _, ?_, ?_⟩
  · rw [Activation.forgetRefs_owners]; exact h.ownerFrame
  · rw [Activation.forgetRefs_owners]; exact h.coverage

theorem advance (h : LoanSafeMachine before callers previous external world active)
    {final : World} {after : Activation} {act : Action}
    (run : Derived.action world active callers act = some (final, after))
    (safe : LoanSafeState after.state) (separate : after.RootsSeparate callers)
    (memoryBound : before.memory.length ≤ final.memory.length)
    (fresh : ∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) :
    LoanSafeMachine before callers previous external final after := by
  have step := Derived.action_spec h.valid h.callersValid h.wellFormed act run
  obtain ⟨r, scan, _, kept⟩ := step.suspended
  have same := (scanCallers_spec h.callersValid scan).unique (h.previousCallers.transport h.kept)
  rw [same] at kept
  obtain ⟨_, _, _, frame, coverage⟩ := Derived.action_owner_resources h.valid h.callersValid h.wellFormed act h.ownerFrame h.coverage run
  exact ⟨h.beforeWellFormed, h.previousCallers, h.kept.trans kept, step.valid, step.wellFormed,
    separate, memoryBound, fresh, safe, frame, coverage⟩

theorem storageLive (h : LoanSafeMachine before callers previous external world active) {slot : Nat}
    (bound : slot < active.count) (unbound : active.roots slot = none) :
    let final := world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])
    let after : Activation := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty}
    Derived.storageLive world active callers slot = some (final, after) ∧
      LoanSafeMachine before callers previous external final after := by
  dsimp only
  have run := Derived.storageLive_complete h.valid h.callersValid bound unbound
  refine ⟨run, h.advance (act := .storageLive slot) run (h.safe.clear slot)
    (h.separate.set_fresh h.callersValid slot _ (Nat.le_refl _)) ?_ ?_⟩
  · rw [(world.allocate_spec _ _).2.2.2.2]
    exact h.memoryBound.trans (by omega)
  · intro index binding hb
    by_cases same : index = slot
    · subst index
      simp only [Roots.set, ite_true, Option.some.injEq] at hb
      cases hb
      exact h.memoryBound
    · exact h.fresh index binding (by simpa only [Roots.set, same, ite_false] using hb)

theorem assign_empty (h : LoanSafeMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (uninitialized : world.memory[binding.address]? = some (.node .tuple 0 []))
    {rhs : Expr} {value : Value} {middle : State}
    (source : SourceEval.expression active.state rhs = some (value, middle)) (empty : middle slot = .empty)
    (safeMiddle : LoanSafeState middle) (safeValue : LoanSafe (Slot.ofValue value))
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      AllowedExpr world active.roots (current.loans ++ suspended.reads) rhs) :
    ∃ cell, Derived.assign world active callers slot rhs = some (world.write binding.address cell,
        {active with state := middle.set slot (Slot.ofValue value)}) ∧
      LoanSafeMachine before callers previous external (world.write binding.address cell)
        {active with state := middle.set slot (Slot.ofValue value)} := by
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := slot) (active := {active with state := middle}) safeMiddle
    uninitialized (Or.inl rfl) h.previousCallers h.beforeWellFormed h.kept (h.fresh slot binding hb)
  obtain ⟨cell, run⟩ := Derived.assign_complete h.valid h.callersValid h.wellFormed h.separate h.ownerFrame hb source empty moves loans
    (fun _ _ scanned _ => Derived.ExpressionLoansAvoid.of_safe scanned.frame source safeValue uninitialized (Or.inl rfl))
  refine ⟨cell, run, h.advance (act := .assign slot rhs) run (safeMiddle.set slot safeValue) h.separate ?_ h.fresh⟩
  simpa only [World.write, List.length_set] using h.memoryBound

theorem move_reference (h : LoanSafeMachine before callers previous external world active)
    {current suspended : Resources} (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {value : Value} (initialized : active.state slot = .shared value) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move (.local slot)) :=
  allowed_shared_local h.valid h.separate h.ownerFrame h.safe scanned callerView
    h.previousCallers h.beforeWellFormed h.kept hb (h.fresh slot binding hb) initialized

end LoanSafeMachine
end SubtreeProofs.Rust.SourceEval.Addressed
