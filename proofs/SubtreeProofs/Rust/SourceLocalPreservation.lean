module

public import SubtreeProofs.Rust.SourceQueryLoanOrigins

/-! Source-local mutation certificates distinguish observing a query reference
from moving it. Addressing and copying a query preserve its mask; moves mutate
only the selected base local. These facts feed actual query-origin transport. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LocalPreservation

open LookupSource Partial

def operand (index : Nat) : Operand → Bool
  | .move place => decide (index ≠ (splitPlace place).1)
  | _ => true

def operands (index : Nat) (args : List Operand) : Bool := args.all (operand index)

def expression (index : Nat) : Expr → Bool
  | .use op => operand index op
  | .address _ => true
  | .aggregate _ _ args => operands index args
  | .less left right => operand index left && operand index right

def action (index : Nat) : Action → Bool
  | .storageLive slot | .storageDead slot | .drop slot => decide (index ≠ slot)
  | .assign slot rhs => decide (index ≠ slot) && expression index rhs
  | .call _ args slot => decide (index ≠ slot) && operands index args
  | .fakeRead _ => true
  | .undefinedBehavior => false

theorem operand_same (index : Nat) {state after : State} {op : Operand} {value : Value}
    (safe : operand index op = true) (run : SourceEval.operand state op = some (value, after)) : after index = state index := by
  cases op with
  | move place => exact Partial.Locals.move_other run index (of_decide_eq_true safe)
  | copy place => rw [(SourceEval.copy_nonowning run).1]
  | boolean _ => cases run; rfl
  | number value =>
    simp only [SourceEval.operand] at run
    split at run
    next => cases run; rfl
    next => cases run

theorem operands_same (index : Nat) {args : List Operand} {state after : State} {values : List Value}
    (safe : operands index args = true) (run : SourceEval.operands state args = some (values, after)) :
    after index = state index := by
  induction args generalizing state values with
  | nil => cases run; rfl
  | cons first rest ih =>
    have all := List.all_eq_true.mp safe
    simp only [SourceEval.operands, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨value, middle⟩, step, ⟨more, final⟩, tail, last⟩ := run
    cases last
    exact (ih (List.all_eq_true.mpr (fun op member => all op (List.mem_cons_of_mem _ member))) tail).trans
      (operand_same index (all first (by simp)) step)

theorem expression_same (index : Nat) {rhs : Expr} {state after : State} {value : Value}
    (safe : expression index rhs = true) (run : SourceEval.expression state rhs = some (value, after)) :
    after index = state index := by
  cases rhs with
  | use op => exact operand_same index safe run
  | address place =>
    simp only [SourceEval.expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨value, _, same⟩ := run
    exact congrFun (Prod.mk.inj (Option.some.inj same)).2.symm index
  | aggregate kind tag args =>
    simp only [SourceEval.expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨values, middle⟩, argsRun, same⟩ := run
    cases same
    exact operands_same index safe argsRun
  | less left right =>
    have parts := Bool.and_eq_true_iff.mp safe
    simp only [SourceEval.expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨leftValue, middle⟩, leftRun, ⟨rightValue, final⟩, rightRun, rest⟩ := run
    have first := operand_same index parts.1 leftRun
    have second := operand_same index parts.2 rightRun
    cases leftValue <;> cases rightValue <;> try cases rest
    simp only [Option.bind_eq_some_iff] at rest
    obtain ⟨answer, _, same⟩ := rest
    cases same
    exact second.trans first

theorem action_same (index : Nat) {call : Calls} {act : Action} {state after : State} {cost : Cost}
    (safe : action index act = true) (run : SourceEval.action call state act = some (after, cost)) :
    after index = state index := by
  cases act with
  | storageLive slot | storageDead slot | drop slot =>
    all_goals cases run; simp only [Partial.Locals.set, of_decide_eq_true safe, ite_false]
  | assign slot rhs =>
    have parts := Bool.and_eq_true_iff.mp safe
    simp only [SourceEval.action, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨value, middle⟩, expr, same⟩ := run
    cases same
    simpa only [Partial.Locals.set, of_decide_eq_true parts.1, ite_false] using expression_same index parts.2 expr
  | call function args slot =>
    have parts := Bool.and_eq_true_iff.mp safe
    simp only [SourceEval.action, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨values, middle⟩, argsRun, ⟨value, work⟩, _, same⟩ := run
    cases same
    simpa only [Partial.Locals.set, of_decide_eq_true parts.1, ite_false] using operands_same index parts.2 argsRun
  | fakeRead _ => cases run; rfl
  | undefinedBehavior => cases safe

end SubtreeProofs.Rust.SourceEval.LocalPreservation
