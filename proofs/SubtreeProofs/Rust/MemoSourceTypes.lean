module

public import SubtreeProofs.Rust.LookupTypedCode
public import SubtreeProofs.Rust.MemoSourceFrontend

/-! Independent lifetime-erased signatures of the actual memo helpers. Insertion
consumes an owned table value and borrows its keys/result; the generic Box
signature transfers exactly its single argument into an owned payload. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Types

open LookupSource LookupSource.Heap LookupSource.SourceTypes

def inputs : Function → List Ty
  | .copyWord => [.shared (.adt .word)]
  | .copyResult => [.shared (.adt .embedding)]
  | .concatenate => [.shared (.adt .word), .shared (.adt .word)]
  | .insert => [.adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)]
  | .boxNew => []

def output : Function → Ty
  | .copyWord | .concatenate => .adt .word
  | .copyResult => .adt .embedding
  | .insert => .adt .table
  | .boxNew => .tuple []

def callOutput (function : Function) (args : List Ty) : Option Ty :=
  if function = .boxNew then
    match args with
    | [inner] => some (.owned inner)
    | _ => none
  else if sameList args (inputs function) then some (output function) else none

abbrev checkCode (locals : List Ty) (result : Ty) : MemoSource.Code → Bool :=
  checkCodeWith callOutput locals result

abbrev CodeConstraints (locals : List Ty) (result : Ty) : MemoSource.Code → Prop :=
  CodeConstraintsWith callOutput locals result

end SubtreeProofs.Rust.MemoSource.Types
