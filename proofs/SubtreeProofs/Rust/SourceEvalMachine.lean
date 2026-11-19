module

public import SubtreeProofs.Rust.SourceEvalOperands

/-! Evaluator primitive execution over partial locals, reusing the shared
source-control executor. Reads/moves, normal destruction and callee work are
explicit. This is the snapshot profile; typed addressed safety is separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval

open LookupSource LookupSource.Partial

inductive Function where
  | copyWord | compare | copyResult | lookup | concatenate | insert
  | chooseLonger | evaluate | maximum | boxNew | checkedAdd
  deriving DecidableEq, Repr

def arity : Function → Nat
  | .copyWord | .copyResult | .boxNew => 1
  | .compare | .concatenate | .chooseLonger | .maximum | .checkedAdd => 2
  | .lookup | .evaluate => 3
  | .insert => 4

def entryEvents : Function → LookupEvents.Events
  | .copyWord => { copyNodes := 1 }
  | .compare => { compareNodes := 1 }
  | .copyResult => { resultCopies := 1 }
  | .lookup => { lookupNodes := 1 }
  | .boxNew => { allocations := 1 }
  | _ => {}

structure Cost where
  work : LookupSource.Cost := {}
  destroyed : DropWork := {}
  solverCalls : Nat := 0

def Cost.plus (first second : Cost) : Cost :=
  ⟨first.work.plus second.work, first.destroyed.plus second.destroyed,
    first.solverCalls + second.solverCalls⟩

def Cost.local (steps : Nat) (destroyed : DropWork := {}) : Cost :=
  ⟨⟨steps + destroyed.visits, {}⟩, destroyed, 0⟩

def Cost.entry (function : Function) : Cost :=
  ⟨⟨1, entryEvents function⟩, {}, if function = .evaluate then 1 else 0⟩

abbrev Calls := Function → List Value → Option (Value × Cost)

inductive Action where
  | storageLive : Nat → Action
  | storageDead : Nat → Action
  | assign : Nat → Expr → Action
  | call : Function → List Operand → Nat → Action
  | drop : Nat → Action
  | fakeRead : Place → Action
  | undefinedBehavior
  deriving DecidableEq

abbrev Code := Control.Tree Action

def Action.weight : Action → Nat
  | .storageLive _ | .storageDead _ | .drop _ | .fakeRead _ | .undefinedBehavior => 1
  | .assign _ value => 1 + value.weight
  | .call _ args _ => 1 + (args.map Operand.weight).sum

def action (call : Calls) (state : State) (instruction : Action) : Option (State × Cost) :=
  match instruction with
  | .storageLive slot | .storageDead slot => some (state.set slot .empty, Cost.local instruction.weight)
  | .assign slot rhs => do
    let (value, after) ← expression state rhs
    some (after.set slot (Slot.ofValue value), Cost.local instruction.weight)
  | .call function args slot => do
    let (values, after) ← operands state args
    let (value, work) ← call function values
    some (after.set slot (Slot.ofValue value), (Cost.local instruction.weight).plus work)
  | .drop slot =>
    let (after, destroyed) := state.drop slot
    some (after, Cost.local instruction.weight destroyed)
  | .fakeRead _ => some (state, Cost.local instruction.weight)
  | .undefinedBehavior => none

/-- The source switch inspects a retained constructor tag, even after a
field move. Value scrutinees are the existing boolean operand fragment. -/
def scrutinee (state : State) : LookupSource.Scrutinee → Option (Key × State)
  | .discriminant place => do
    let (slot, path) := splitPlace place
    match ← (state slot).get path with
    | .node kind variant _ => some (.variant kind variant, state)
    | _ => none
  | .value op => do
    let (value, after) ← match op with
      | .move slot => operand state (.move (.local slot))
      | .copy place => operand state (.copy place)
      | .boolean value => operand state (.boolean value)
    match value with
    | .boolean value => some (.boolean value, after)
    | _ => none

inductive Outcome where
  | next : State → Outcome
  | returned : Value → Outcome

def nextState : Outcome → Option State
  | .next state => some state
  | .returned _ => none

def returnValue (state : State) : Option (Outcome × Cost) := do
  let value ← (state 0).materialize
  some (.returned value, Cost.local 1)

def exec (call : Calls) : Code → State → Option (Outcome × Cost) :=
  Control.execWith (action call) scrutinee returnValue Outcome.next nextState
    {} Cost.plus (fun scrut => Cost.local (1 + scrut.weight))

theorem exec_step (call : Calls) (instruction : Action) (rest : Code) (state : State) :
    exec call (.step instruction rest) state = (do
      let (next, first) ← action call state instruction
      let (result, last) ← exec call rest next
      some (result, first.plus last)) := rfl

theorem exec_ret (call : Calls) (state : State) : exec call .ret state = returnValue state := rfl

def initialState (args : List Value) : State := Partial.Locals.lift (initialEnv args)

def run (body : Function → Code) : Nat → Calls
  | 0, _, _ => none
  | fuel + 1, function, args =>
    match function, args with
    | .boxNew, [value] => some (.boxed value, Cost.entry function)
    | .boxNew, _ => none
    | .checkedAdd, [.number left, .number right] =>
      if left < 2^32 ∧ right < 2^32 then
        some (encodeNumberOption (checkedAdd32 left right), Cost.entry function)
      else none
    | .checkedAdd, _ => none
    | _, _ => do
      let (result, work) ← exec (run body fuel) (body function) (initialState args)
      match result with
      | .next _ => none
      | .returned value => some (value, (Cost.entry function).plus work)

theorem action_drop (call : Calls) (state : State) (slot : Nat) :
    action call state (.drop slot) = some (state.set slot .empty, Cost.local 1 (state slot).dropWork) := rfl

theorem action_drop_other (call : Calls) (state : State) (slot other : Nat) (hne : other ≠ slot) :
    ∃ after cost, action call state (.drop slot) = some (after, cost) ∧ after other = state other ∧
      cost.destroyed = (state slot).dropWork ∧ cost.work.steps = 1 + (state slot).dropWork.visits := by
  refine ⟨state.set slot .empty, Cost.local 1 (state slot).dropWork, rfl, ?_, rfl, rfl⟩
  simp only [Partial.Locals.set, hne, ite_false]

theorem run_checkedAdd (body : Function → Code) (fuel : Nat) (left right : Aeneas.Std.U32) :
    run body (fuel + 1) .checkedAdd [.number left.val, .number right.val] =
      some (encodeNumberOption ((Aeneas.Std.U32.checked_add left right).map (fun value => value.val)), Cost.entry .checkedAdd) := by
  have hl : left.val < 2^32 := left.hmax
  have hr : right.val < 2^32 := right.hmax
  simp only [run, hl, hr, and_self, ite_true, checkedAdd32_native]

end SubtreeProofs.Rust.SourceEval
