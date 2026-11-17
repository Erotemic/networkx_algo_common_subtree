module

public import SubtreeProofs.Rust.LookupHeapMemory

/-! Independent field signatures and scalar bounds for represented lookup
values. This is finite read-only heap typing, not a Rust borrow checker or a
proof that every accepted JSON declaration has these field signatures. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

inductive Ty where
  | boolean
  | u32
  | adt : Kind → Ty
  | tuple : List Ty → Ty
  | shared : Ty → Ty
  | owned : Ty → Ty
  deriving Repr

inductive Shape : Kind → Nat → List Ty → Ty → Prop where
  | emptyWord : Shape .word 0 [] (.adt .word)
  | pairWord : Shape .word 1 [.owned (.adt .word), .owned (.adt .word)] (.adt .word)
  | emptyTable : Shape .table 0 [] (.adt .table)
  | entryTable : Shape .table 1 [.owned (.adt .entry), .owned (.adt .table)] (.adt .table)
  | entry : Shape .entry 0 [.adt .word, .adt .word, .adt .embedding] (.adt .entry)
  | embedding : Shape .embedding 0 [.adt .word, .u32] (.adt .embedding)
  | none : Shape .optional 0 [] (.adt .optional)
  | some : Shape .optional 1 [.adt .embedding] (.adt .optional)
  | tuple (types : List Ty) : Shape .tuple 0 types (.tuple types)

mutual
  inductive SnapshotTyped : Value → Ty → Prop where
    | boolean (value : Bool) : SnapshotTyped (.boolean value) .boolean
    | number {value : Nat} : value < 2 ^ 32 → SnapshotTyped (.number value) .u32
    | node {kind : Kind} {variant : Nat} {values : List Value} {types : List Ty} {ty : Ty} :
        Shape kind variant types ty → SnapshotFieldsTyped values types →
        SnapshotTyped (.node kind variant values) ty
    | shared {value : Value} {ty : Ty} :
        SnapshotTyped value ty → SnapshotTyped (.reference value) (.shared ty)
    | owned {value : Value} {ty : Ty} :
        SnapshotTyped value ty → SnapshotTyped (.boxed value) (.owned ty)

  inductive SnapshotFieldsTyped : List Value → List Ty → Prop where
    | nil : SnapshotFieldsTyped [] []
    | cons {value : Value} {ty : Ty} {values : List Value} {types : List Ty} :
        SnapshotTyped value ty → SnapshotFieldsTyped values types →
        SnapshotFieldsTyped (value :: values) (ty :: types)
end

mutual
  inductive Typed (memory : Memory) : Cell → Ty → Prop where
    | boolean (value : Bool) : Typed memory (.boolean value) .boolean
    | number {value : Nat} : value < 2 ^ 32 → Typed memory (.number value) .u32
    | node {kind : Kind} {variant : Nat} {cells : List Cell} {types : List Ty} {ty : Ty} :
        Shape kind variant types ty → FieldsTyped memory cells types →
        Typed memory (.node kind variant cells) ty
    | shared {pointer : Pointer} {cell : Cell} {ty : Ty} :
        read memory pointer = some cell → Typed memory cell ty →
        Typed memory (.shared pointer) (.shared ty)
    | owned {address : Nat} {cell : Cell} {ty : Ty} :
        memory[address]? = some cell → Typed memory cell ty →
        Typed memory (.owned address) (.owned ty)

  inductive FieldsTyped (memory : Memory) : List Cell → List Ty → Prop where
    | nil : FieldsTyped memory [] []
    | cons {cell : Cell} {ty : Ty} {cells : List Cell} {types : List Ty} :
        Typed memory cell ty → FieldsTyped memory cells types →
        FieldsTyped memory (cell :: cells) (ty :: types)
end

mutual
  theorem Represents.typed {memory : Memory} {cell : Cell} {value : Value} {ty : Ty}
      (hr : Represents memory cell value) (ht : SnapshotTyped value ty) : Typed memory cell ty := by
    cases ht with
    | boolean b => cases hr; exact .boolean b
    | number hb => cases hr; exact .number hb
    | node hs ht => cases hr with
      | node hr => exact .node hs (hr.typed ht)
    | shared ht => cases hr with
      | shared hp hr => exact .shared hp (hr.typed ht)
    | owned ht => cases hr with
      | owned hp hr => exact .owned hp (hr.typed ht)

  theorem RepresentsFields.typed {memory : Memory} {cells : List Cell}
      {values : List Value} {types : List Ty} (hr : RepresentsFields memory cells values)
      (ht : SnapshotFieldsTyped values types) : FieldsTyped memory cells types := by
    cases ht with
    | nil => cases hr; exact .nil
    | cons ht hts => cases hr with
      | cons hr hrs => exact .cons (hr.typed ht) (hrs.typed hts)
end

open verified_ordered_core in
theorem word_typed (word : BalancedWord) : SnapshotTyped (encodeWord word) (.adt .word) := by
  induction word with
  | Empty => exact .node .emptyWord .nil
  | Pair head tail hh ht => exact .node .pairWord (.cons (.owned hh) (.cons (.owned ht) .nil))

open verified_ordered_core in
theorem result_typed (result : CommonEmbedding) :
    SnapshotTyped (encodeResult result) (.adt .embedding) :=
  .node .embedding (.cons (word_typed result.word) (.cons (.number result.edges.hmax) .nil))

open verified_ordered_core in
theorem table_typed (table : MemoTable) : SnapshotTyped (encodeTable table) (.adt .table) := by
  induction table with
  | Empty => exact .node .emptyTable .nil
  | Entry entry rest ih =>
    exact .node .entryTable (.cons (.owned (.node .entry
      (.cons (word_typed entry.left) (.cons (word_typed entry.right)
        (.cons (result_typed entry.result) .nil))))) (.cons (.owned ih) .nil))

open verified_ordered_core in
theorem option_typed (value : Option CommonEmbedding) :
    SnapshotTyped (encodeOption value) (.adt .optional) := by
  cases value with
  | none => exact .node .none .nil
  | some value => exact .node .some (.cons (result_typed value) .nil)

end SubtreeProofs.Rust.LookupSource.Heap
