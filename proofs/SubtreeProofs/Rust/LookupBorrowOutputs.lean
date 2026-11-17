module

public import SubtreeProofs.Rust.LookupBorrowLoans

/-! Ordinary lookup helpers return data containing no shared loans, including
inside owned heap payloads. This is derived from independent field typing,
not merely from a shallow check of the returned constructor. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

mutual
  inductive Closed : Ty → Prop where
    | boolean : Closed .boolean
    | u32 : Closed .u32
    | adt (kind : Kind) : Closed (.adt kind)
    | tuple {types : List Ty} : ClosedFields types → Closed (.tuple types)
    | owned {inner : Ty} : Closed inner → Closed (.owned inner)
    | option {inner : Ty} : Closed inner → Closed (.option inner)

  inductive ClosedFields : List Ty → Prop where
    | nil : ClosedFields []
    | cons {ty : Ty} {types : List Ty} : Closed ty → ClosedFields types → ClosedFields (ty :: types)
end

mutual
  inductive Unborrowed (memory : Memory) : Cell → Prop where
    | boolean (value : Bool) : Unborrowed memory (.boolean value)
    | number (value : Nat) : Unborrowed memory (.number value)
    | node {kind : Kind} {variant : Nat} {cells : List Cell} :
        UnborrowedFields memory cells → Unborrowed memory (.node kind variant cells)
    | owned {address : Nat} {cell : Cell} :
        memory[address]? = some cell → Unborrowed memory cell → Unborrowed memory (.owned address)

  inductive UnborrowedFields (memory : Memory) : List Cell → Prop where
    | nil : UnborrowedFields memory []
    | cons {cell : Cell} {cells : List Cell} :
        Unborrowed memory cell → UnborrowedFields memory cells → UnborrowedFields memory (cell :: cells)
end

theorem shape_closed {kind : Kind} {variant : Nat} {types : List Ty} {ty : Ty}
    (hs : Shape kind variant types ty) (hc : Closed ty) : ClosedFields types := by
  cases hs <;> cases hc
  all_goals repeat first | assumption | constructor

mutual
  theorem typed_unborrowed {memory : Memory} {cell : Cell} {ty : Ty}
      (h : Typed memory cell ty) (hc : Closed ty) : Unborrowed memory cell :=
    match h with
    | .boolean value => .boolean value
    | .number _ => .number _
    | .node shape fields => .node (fieldsTyped_unborrowed fields (shape_closed shape hc))
    | .shared _ _ => by cases hc
    | .owned hr child => by cases hc with | owned hc => exact .owned hr (typed_unborrowed child hc)

  theorem fieldsTyped_unborrowed {memory : Memory} {cells : List Cell} {types : List Ty}
      (h : FieldsTyped memory cells types) (hc : ClosedFields types) : UnborrowedFields memory cells :=
    match h with
    | .nil => .nil
    | .cons first rest => by cases hc with | cons hh ht => exact .cons (typed_unborrowed first hh) (fieldsTyped_unborrowed rest ht)
end

theorem ordinary_output_closed (function : Function) (hf : function ≠ .boxNew) : Closed (SourceTypes.output function) := by
  cases function <;> first | contradiction | constructor

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
