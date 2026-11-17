module

public import SubtreeProofs.Rust.LookupStackCode
public import SubtreeProofs.Rust.LookupSourceFrontend
public import SubtreeProofs.Rust.LookupHeapPrimitives

/-! Explicit local-storage allocation and initialization states. Both dead and
allocated-uninitialized slots erase to an empty value environment, but writes
are permitted only to allocated slots. Pointer/variant validity is separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Stack

open Heap

inductive Status where
  | dead
  | empty
  | full
  deriving DecidableEq, Repr

abbrev State := List Status

def status (state : State) (slot : Nat) : Status := state[slot]?.getD .dead

def Matches : Status → Option Cell → Prop
  | .dead, none | .empty, none => True
  | .full, some _ => True
  | _, _ => False

def StateRep (state : State) (env : Locals) : Prop := ∀ index, Matches (status state index) (env index)

theorem StateRep.empty {state : State} {env : Locals} (h : StateRep state env)
    {slot : Nat} (hs : status state slot ≠ .full) : env slot = none := by
  have hx := h slot
  cases hp : status state slot <;> cases hc : env slot <;> simp_all [Matches]

theorem StateRep.full {state : State} {env : Locals} (h : StateRep state env)
    {slot : Nat} {cell : Cell} (hc : env slot = some cell) : status state slot = .full := by
  have hx := h slot
  cases hp : status state slot <;> simp_all [Matches]

theorem status_set (state : State) (slot : Nat) (value : Status) (hb : slot < state.length) (index : Nat) :
    status (state.set slot value) index = if index = slot then value else status state index := by
  by_cases hi : index = slot
  · subst index; simp [status, List.getElem?_set_self hb]
  · simp [status, hi]

theorem StateRep.set {state : State} {env : Locals} (h : StateRep state env)
    (slot : Nat) (hb : slot < state.length) {value : Status} {cell : Option Cell} (hm : Matches value cell) :
    StateRep (state.set slot value) (env.set slot cell) := by
  intro index
  rw [status_set state slot value hb index]
  by_cases hi : index = slot
  · simpa [Locals.set, hi] using hm
  · simpa [Locals.set, hi] using h index

def placeReady (state : State) : Place → Bool
  | .local slot => status state slot == .full
  | .deref parent | .field parent _ _ => placeReady state parent

def inferOperand (state : State) : Operand → Option State
  | .boolean _ => some state
  | .copy place => if placeReady state place then some state else none
  | .move slot => if slot < state.length && status state slot == .full then some (state.set slot .empty) else none

def inferOperands : State → List Operand → Option State
  | state, [] => some state
  | state, first :: rest => do inferOperands (← inferOperand state first) rest

def inferRValue (state : State) : RValue → Option State
  | .use op => inferOperand state op
  | .address place => if placeReady state place then some state else none
  | .aggregate _ _ args => inferOperands state args

def inferScrutinee (state : State) : Scrutinee → Option State
  | .value op => inferOperand state op
  | .discriminant place => if placeReady state place then some state else none

def store (state : State) (slot : Nat) : Option State :=
  if slot < state.length && status state slot != .dead then some (state.set slot .full) else none

def inferAction (state : State) : Control.Action → Option State
  | .storageLive slot => if slot < state.length then some (state.set slot .empty) else none
  | .storageDead slot => if slot < state.length then some (state.set slot .dead) else none
  | .assign slot rhs => do store (← inferRValue state rhs) slot
  | .call function args slot =>
    if args.length == Frontend.arity function then do store (← inferOperands state args) slot else none
  | .dropConditional slot =>
    if slot < state.length && status state slot == .empty then some state else none

def verify : Code → State → (State → Bool) → Bool
  | .done, state, post => post state
  | .ret, state, _ => status state 0 == .full
  | .step action rest, state, post =>
    match inferAction state action with
    | none => false
    | some next => verify rest next post
  | .branch scrut _ _ yes no rest, state, post =>
    match inferScrutinee state scrut with
    | none => false
    | some next => verify yes next (fun state => verify rest state post) && verify no next (fun state => verify rest state post)

def initial (count arguments : Nat) : State :=
  .dead :: List.replicate arguments .full ++ List.replicate (count - (arguments + 1)) .dead

end SubtreeProofs.Rust.LookupSource.Stack
