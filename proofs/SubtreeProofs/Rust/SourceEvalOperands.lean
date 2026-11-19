module

public import SubtreeProofs.Rust.SourceEvalScalar
public import SubtreeProofs.Rust.LookupSourceControl

/-! Partial-local operands and expressions for the evaluator. Copies exclude
owned values; references use snapshot readback at this stage. Addressed loans
and actual source certificates remain separate composition obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval

open LookupSource LookupSource.Partial

abbrev State := Partial.Locals

inductive Operand where
  | move : Place → Operand
  | copy : Place → Operand
  | boolean : Bool → Operand
  | number : Nat → Operand
  deriving DecidableEq

def Operand.weight : Operand → Nat
  | .move place | .copy place => place.weight
  | .boolean _ | .number _ => 1

def operand (state : State) : Operand → Option (Value × State)
  | .move place => state.move place
  | .copy place => do
    let value ← state.read place
    match value with
    | .boolean _ | .reference _ => some (value, state)
    | .number n => if n < 2^32 then some (value, state) else none
    | _ => none
  | .boolean value => some (.boolean value, state)
  | .number value => if value < 2^32 then some (.number value, state) else none

def operands : State → List Operand → Option (List Value × State)
  | state, [] => some ([], state)
  | state, first :: rest => do
    let (value, middle) ← operand state first
    let (values, after) ← operands middle rest
    some (value :: values, after)

inductive Expr where
  | use : Operand → Expr
  | address : Place → Expr
  | aggregate : Kind → Nat → List Operand → Expr
  | less : Operand → Operand → Expr
  deriving DecidableEq

def Expr.weight : Expr → Nat
  | .use op => op.weight
  | .address place => 1 + place.weight
  | .aggregate _ _ args => 1 + (args.map Operand.weight).sum
  | .less left right => 1 + left.weight + right.weight

def expression (state : State) : Expr → Option (Value × State)
  | .use op => operand state op
  | .address place => do
    let value ← state.read place
    some (.reference value, state)
  | .aggregate kind variant args => do
    let (values, after) ← operands state args
    some (.node kind variant values, after)
  | .less left right => do
    let (left, middle) ← operand state left
    let (right, after) ← operand middle right
    match left, right with
    | .number left, .number right => do
      let answer ← less32 left right
      some (.boolean answer, after)
    | _, _ => none

theorem copy_nonowning {state after : State} {place : Place} {value : Value}
    (h : operand state (.copy place) = some (value, after)) :
    after = state ∧ state.read place = some value ∧ (Slot.ofValue value).dropWork.boxes = 0 := by
  simp only [operand] at h
  cases hr : state.read place with
  | none => simp [hr] at h
  | some result =>
    simp only [hr, bind, Option.bind] at h
    cases result with
    | boolean b | reference target =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, by simp [Slot.ofValue, Slot.dropWork]⟩
    | number n =>
      by_cases hb : n < 2^32
      · simp only [hb, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, by simp [Slot.ofValue, Slot.dropWork]⟩
      · simp only [hb, ite_false] at h
        cases h
    | node _ _ _ | boxed _ => cases h

theorem address_nonowning {state after : State} {place : Place} {value : Value}
    (h : expression state (.address place) = some (value, after)) :
    after = state ∧ (Slot.ofValue value).dropWork.boxes = 0 := by
  simp only [expression] at h
  cases hr : state.read place with
  | none => simp [hr] at h
  | some result =>
    simp only [hr, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [Slot.ofValue, Slot.dropWork]⟩

theorem move_transfer {state after : State} {place : Place} {value : Value}
    (h : operand state (.move place) = some (value, after)) :
    state.read place = some value ∧ ∃ remaining,
      after = state.set (splitPlace place).1 remaining ∧
      remaining.get (splitPlace place).2 = some .empty ∧
      (state (splitPlace place).1).dropWork = (Slot.ofValue value).dropWork.plus remaining.dropWork :=
  Partial.Locals.move_spec h

end SubtreeProofs.Rust.SourceEval
