module

public import SubtreeProofs.Rust.SourceHeapReachability

/-! Executable finite read-resource tracing from a cell and initialization
metadata. This traverses actual shared/owned pointers and validates their value
shape. It is ghost bookkeeping for the declared source interpretation, not an
additional algorithm executed by production Rust or a new runtime cost claim. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

mutual
  def traceGraph (memory : Memory) (cell : Cell) : Value → Option (List Nat)
    | .boolean b => match cell with
      | .boolean actual => if b = actual then some [] else none
      | _ => none
    | .number n => match cell with
      | .number actual => if n = actual then some [] else none
      | _ => none
    | .node kind tag values => match cell with
      | .node actual variant cells => if kind = actual ∧ tag = variant then traceGraphFields memory cells values else none
      | _ => none
    | .reference value => match cell with
      | .shared pointer => do
        let child ← read memory pointer
        let guards ← traceGraph memory child value
        some (guards ++ [pointer.root])
      | _ => none
    | .boxed value => match cell with
      | .owned address => do
        let child ← memory[address]?
        let guards ← traceGraph memory child value
        some (guards ++ [address])
      | _ => none
  termination_by value => sizeOf value

  def traceGraphFields (memory : Memory) : List Cell → (values : List Value) → Option (List Nat)
    | [], [] => some []
    | cell :: cells, value :: values => do
      let first ← traceGraph memory cell value
      let rest ← traceGraphFields memory cells values
      some (first ++ rest)
    | _, _ => none
  termination_by _ values => sizeOf values
end

mutual
  theorem Graph.trace {memory : Memory} {cell : Cell} {value : Value} {guards : List Nat}
      (h : Graph memory cell value guards) : traceGraph memory cell value = some guards := by
    cases h with
    | boolean _ | number _ => simp only [traceGraph, ↓reduceIte]
    | node fields => simp only [traceGraph, and_self, ↓reduceIte, fields.trace]
    | shared hr child => simp only [traceGraph, hr, child.trace, Bind.bind, Option.bind]
    | owned hr child => simp only [traceGraph, hr, child.trace, Bind.bind, Option.bind]

  theorem GraphFields.trace {memory : Memory} {cells : List Cell} {values : List Value} {guards : List Nat}
      (h : GraphFields memory cells values guards) : traceGraphFields memory cells values = some guards := by
    cases h with
    | nil => simp only [traceGraphFields]
    | cons first rest => simp only [traceGraphFields, first.trace, rest.trace, Bind.bind, Option.bind]
end

theorem Graph.guards_unique {memory : Memory} {cell : Cell} {value : Value} {first second : List Nat}
    (h₁ : Graph memory cell value first) (h₂ : Graph memory cell value second) : first = second :=
  Option.some.inj (h₁.trace.symm.trans h₂.trace)

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
