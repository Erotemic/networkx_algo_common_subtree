module

public import SubtreeProofs.Rust.SourceEvalMachine
public import SubtreeProofs.Rust.LookupTypedCode

/-! Lifetime-erased signatures and expression constraints for the complete
source profile. Constructor checking uses the independent shared `Heap.Shape`
relation, including parameterized options. Initialization, storage and loans
are separate properties. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap SourceTypes

/-- An owned projection route cannot cross a shared reference. Moving the
reference value itself remains permitted. -/
def inferMovePlace (locals : List Ty) : Place → Option Ty
  | .local slot => locals[slot]?
  | .deref parent => do
    match ← inferMovePlace locals parent with
    | .owned inner => some inner
    | _ => none
  | .field parent variant index => do fieldType (← inferMovePlace locals parent) variant index

theorem inferMovePlace_read {locals : List Ty} (place : Place) {ty : Ty}
    (h : inferMovePlace locals place = some ty) : inferPlace locals place = some ty := by
  induction place generalizing ty with
  | «local» slot => exact h
  | deref parent ih =>
    cases hp : inferMovePlace locals parent with
    | none => simp [inferMovePlace, hp] at h
    | some parentTy =>
      have hr := ih hp
      cases parentTy <;> simp_all [inferMovePlace, inferPlace, deref]
  | field parent variant index ih =>
    cases hp : inferMovePlace locals parent with
    | none => simp [inferMovePlace, hp] at h
    | some parentTy =>
      simpa only [inferPlace, ih hp, bind, Option.bind] using
        (show fieldType parentTy variant index = some ty from by
          simpa only [inferMovePlace, hp, bind, Option.bind] using h)

def inferOperand (locals : List Ty) : SourceEval.Operand → Option Ty
  | .move place => inferMovePlace locals place
  | .copy place => do
    let ty ← inferPlace locals place
    if copyable ty then some ty else none
  | .boolean _ => some .boolean
  | .number n => if n < 2^32 then some .u32 else none

def inferOperands (locals : List Ty) (args : List SourceEval.Operand) : Option (List Ty) :=
  args.mapM (inferOperand locals)

def inputs : SourceEval.Function → List Ty
  | .copyWord => [.shared (.adt .word)]
  | .compare => [.shared (.adt .word), .shared (.adt .word)]
  | .copyResult => [.shared (.adt .embedding)]
  | .lookup => [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)]
  | .concatenate => [.shared (.adt .word), .shared (.adt .word)]
  | .insert => [.adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)]
  | .chooseLonger => [.adt .embedding, .adt .embedding]
  | .evaluate => [.shared (.adt .word), .shared (.adt .word), .adt .table]
  | .maximum => [.shared (.adt .word), .shared (.adt .word)]
  | .checkedAdd => [.u32, .u32]
  | .boxNew => []

def output : SourceEval.Function → Ty
  | .copyWord | .concatenate => .adt .word
  | .compare => .boolean
  | .copyResult | .chooseLonger => .adt .embedding
  | .lookup | .maximum => .adt .optional
  | .insert => .adt .table
  | .evaluate => .tuple [.adt .optional, .adt .table]
  | .checkedAdd => .option .u32
  | .boxNew => .tuple []

def callOutput (function : SourceEval.Function) (args : List Ty) : Option Ty :=
  if function = .boxNew then
    match args with
    | [inner] => some (.owned inner)
    | _ => none
  else if sameList args (inputs function) then some (output function) else none

/-- Aggregates are checked against the destination type: an empty option
alone cannot determine its parameter. -/
def checkExpr (locals : List Ty) (result : Ty) : Expr → Bool
  | .use op => sameResult (inferOperand locals op) (some result)
  | .address place => sameResult (Ty.shared <$> inferPlace locals place) (some result)
  | .aggregate kind variant args =>
    match inferOperands locals args, constructorFields kind variant result with
    | some actual, some expected => sameList actual expected
    | _, _ => false
  | .less left right => same result .boolean &&
      sameResult (inferOperand locals left) (some .u32) &&
      sameResult (inferOperand locals right) (some .u32)

inductive ExprConstraints (locals : List Ty) : Expr → Ty → Prop where
  | use {op : SourceEval.Operand} {ty : Ty} : inferOperand locals op = some ty →
      ExprConstraints locals (.use op) ty
  | address {place : Place} {ty : Ty} : inferPlace locals place = some ty →
      ExprConstraints locals (.address place) (.shared ty)
  | aggregate {kind : Kind} {variant : Nat} {args : List SourceEval.Operand} {types : List Ty} {ty : Ty} :
      inferOperands locals args = some types → Shape kind variant types ty →
      ExprConstraints locals (.aggregate kind variant args) ty
  | less {left right : SourceEval.Operand} :
      inferOperand locals left = some .u32 → inferOperand locals right = some .u32 →
      ExprConstraints locals (.less left right) .boolean

theorem checkExpr_sound {locals : List Ty} {result : Ty} {expr : Expr}
    (h : checkExpr locals result expr = true) : ExprConstraints locals expr result := by
  cases expr with
  | use op =>
    obtain ⟨ty, ho, ht⟩ := sameResult_sound h
    cases ht
    exact .use ho
  | address place =>
    obtain ⟨ty, ho, ht⟩ := sameResult_sound h
    cases ht
    cases hp : inferPlace locals place with
    | none => simp [hp] at ho
    | some inner =>
      simp only [hp, Functor.map, Option.map_some, Option.some.injEq] at ho
      subst result
      exact .address hp
  | aggregate kind variant args =>
    cases ha : inferOperands locals args <;> cases hf : constructorFields kind variant result <;>
      simp only [checkExpr, ha, hf, Bool.false_eq_true] at h
    have he := sameList_eq h
    subst_vars
    exact .aggregate ha (constructorFields_sound hf)
  | less left right =>
    simp only [checkExpr, Bool.and_eq_true_iff] at h
    have he := same_eq h.1.1
    subst result
    obtain ⟨_, hl, ht⟩ := sameResult_sound h.1.2
    cases ht
    obtain ⟨_, hr, ht⟩ := sameResult_sound h.2
    cases ht
    exact .less hl hr

end SubtreeProofs.Rust.SourceEval.Types
