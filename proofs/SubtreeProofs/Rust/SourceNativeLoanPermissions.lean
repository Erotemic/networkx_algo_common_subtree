module

public import SubtreeProofs.Rust.SourceNativeLoanCells
public import SubtreeProofs.Rust.SourceAssignmentTotality
public import SubtreeProofs.Rust.SourceEvalLoanEndings

/-! Native referent structure discharges fresh empty-destination guards and
moves of reference-valued locals. Older suspended graphs may alias freely;
their preserved read bound separates them from fresh callee stack roots. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap verified_ordered_core

theorem NativeData.word (word : BalancedWord) : NativeData (encodeWord word) := by
  induction word with
  | Empty => exact .node (by intro impossible; cases impossible) .nil
  | Pair head tail ihHead ihTail =>
    exact .node (by intro impossible; cases impossible) (.cons (.owned ihHead) (.cons (.owned ihTail) .nil))

theorem NativeData.result (result : CommonEmbedding) : NativeData (encodeResult result) :=
  .node (by intro impossible; cases impossible) (.cons (NativeData.word result.word) (.cons (.number result.edges.val) .nil))

theorem NativeData.table (table : MemoTable) : NativeData (encodeTable table) := by
  induction table with
  | Empty => exact .node (by intro impossible; cases impossible) .nil
  | Entry entry tail ih =>
    exact .node (by intro impossible; cases impossible)
      (.cons (.owned (.node (by intro impossible; cases impossible)
        (.cons (NativeData.word entry.left) (.cons (NativeData.word entry.right) (.cons (NativeData.result entry.result) .nil)))))
        (.cons (.owned ih) .nil))

mutual
  theorem NativeData.loan_safe {value : Value} (h : NativeData value) : LoanSafe (Slot.ofValue value) := by
    cases h with
    | boolean value => simpa only [Slot.ofValue] using LoanSafe.boolean value
    | number value => simpa only [Slot.ofValue] using LoanSafe.number value
    | node _ fields => simpa only [Slot.ofValue] using LoanSafe.node fields.loan_safe
    | owned child => simpa only [Slot.ofValue] using LoanSafe.owned child.loan_safe
  termination_by sizeOf value

  theorem NativeDataFields.loan_safe {values : List Value} (h : NativeDataFields values) : LoanSafeFields (ofFields values) := by
    cases h with
    | nil => simpa only [ofFields] using LoanSafeFields.nil
    | cons first rest => simpa only [ofFields] using LoanSafeFields.cons first.loan_safe rest.loan_safe
  termination_by sizeOf values
end

end SubtreeProofs.Rust.LookupSource.Partial.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def LoanSafeState (state : State) : Prop := ∀ slot, LoanSafe (state slot)

theorem LoanSafeState.set {state : State} (h : LoanSafeState state) (slot : Nat) {part : Slot} (safe : LoanSafe part) :
    LoanSafeState (state.set slot part) := by
  intro index
  by_cases same : index = slot
  · subst index; simpa only [Partial.Locals.set, ite_true] using safe
  · simpa only [Partial.Locals.set, same, ite_false] using h index

theorem LoanSafeState.clear {state : State} (h : LoanSafeState state) (slot : Nat) : LoanSafeState (state.set slot .empty) :=
  h.set slot .empty

theorem LoanSafeState.forget {state : State} (h : LoanSafeState state) (code : Code) (slots : List Nat) :
    LoanSafeState (LoanEnding.forget code slots state) := by
  induction slots generalizing state with
  | nil => exact h
  | cons slot rest ih =>
    rw [LoanEnding.forget_cons]
    cases hs : state slot <;> try exact ih h
    by_cases ended : LoanEnding.endsBeforeObservation slot code = true
    · simp only [ended, ite_true]; exact ih (h.clear slot)
    · simp only [ended, Bool.false_eq_true, ite_false]; exact ih h

theorem LoanSafeState.initial {args : List Value} (safe : ∀ value ∈ args, LoanSafe (Slot.ofValue value)) :
    LoanSafeState (initialState args) := by
  intro slot
  by_cases zero : slot = 0
  · subst slot; exact .empty
  · cases lookup : args[slot - 1]? with
    | none => simp only [initialState, Partial.Locals.lift, initialEnv, zero, ite_false, lookup]; exact .empty
    | some value =>
      simpa only [initialState, Partial.Locals.lift, initialEnv, zero, ite_false, lookup] using safe value (List.mem_of_getElem? lookup)

namespace Derived

theorem RootLoansAllowed.of_safe_preserved {before world : World} {active : Activation} {callers : List Activation}
    {slot : Nat} {binding : Binding} {previous : Resources} {cell : Cell}
    (safe : LoanSafeState active.state) (memory : world.memory[binding.address]? = some cell) (invalid : InvalidLoanCell cell)
    (view : Callers before callers previous) (hw : before.WellFormed) (kept : Preserves before world previous.reads)
    (fresh : before.memory.length ≤ binding.address) : RootLoansAllowed world active callers slot binding := by
  intro remainder suspended remaining callers forbidden
  rcases List.mem_append.mp forbidden with current | old
  · exact remaining.safe_cells (fun index _ => safe index) binding.address current cell memory invalid
  · have bound := view.preserved_read_bound hw kept callers binding.address (callers.loans_subset_reads old)
    omega

theorem PacketLoansAvoid.of_safe {world : World} {packet : ValueCell} {address : Nat} {cell : Cell}
    (safe : LoanSafe (Slot.ofValue packet.2)) (memory : world.memory[address]? = some cell) (invalid : InvalidLoanCell cell) :
    PacketLoansAvoid world packet address := by
  intro loans represented forbidden
  exact represented.safe_cells safe address forbidden cell memory invalid

theorem ExpressionLoansAvoid.of_safe {world : World} {roots : Roots} {frame : Nat} {state middle : State}
    {guards blocked : List Nat} (hf : Frame world frame roots state guards) {rhs : Expr} {value : Value}
    (source : SourceEval.expression state rhs = some (value, middle)) (safe : LoanSafe (Slot.ofValue value))
    {address : Nat} {cell : Cell} (memory : world.memory[address]? = some cell) (invalid : InvalidLoanCell cell) :
    ExpressionLoansAvoid world roots blocked state rhs address := by
  intro packet masks run
  obtain ⟨_, execution, _, _, _⟩ := Addressed.expression_spec hf run
  have same := (Prod.mk.inj (Option.some.inj (execution.symm.trans source))).1
  exact PacketLoansAvoid.of_safe (same ▸ safe) memory invalid

end Derived

theorem allowed_shared_local {before world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (safe : LoanSafeState active.state) {current suspended previous : Resources}
    (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    (view : Callers before callers previous) (hw : before.WellFormed) (kept : Preserves before world previous.reads)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (fresh : before.memory.length ≤ binding.address) {value : Value} (initialized : active.state slot = .shared value) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move (.local slot)) := by
  obtain ⟨_, frame⟩ := ha.2
  obtain ⟨cell, used, memory, _, graph, _⟩ := frame.get hb
  rw [initialized] at graph
  cases graph with
  | @shared pointer value reads graph =>
    apply allowed_local_from_loans ha separate hf callerView hb
    intro forbidden
    rcases List.mem_append.mp forbidden with currentLoan | oldLoan
    · exact scanned.inventory.safe_cells (fun index _ => safe index) binding.address currentLoan _ memory (Or.inr ⟨pointer, rfl⟩)
    · have bound := view.preserved_read_bound hw kept callerView binding.address (callerView.loans_subset_reads oldLoan)
      omega

end SubtreeProofs.Rust.SourceEval.Addressed
