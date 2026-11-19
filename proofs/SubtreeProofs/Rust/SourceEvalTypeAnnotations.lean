module

public import SubtreeProofs.Rust.SourceEvalTypedCode
public import SubtreeProofs.Rust.SourceEvalProgram

/-! Nested type annotations for the expanded source syntax. Place, metadata,
constant-key, layout and type reading reuse the shared checked readers. This
adapter handles projected moves, scalar literals/less-than, live drops and fake
reads without introducing a second source parser. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.TypeReader

open Lean LookupSource Heap
open LookupSource.Frontend hiding Context operand operands rvalue action sequence arity
open LookupSource.TypeReader hiding operandAnnotations rvalueAnnotations actionAnnotations statementAnnotations Definition Program definition read check

abbrev Context := LookupSource.TypeReader.Context

def operandAnnotations (ctx : Context) (locals : List Ty) (fuel : Nat) (json : Json) : Read Unit := do
  let op ← SourceEval.Frontend.operand (localContext ctx locals) fuel json
  let actual ← required (Types.inferOperand locals op)
  let (constructor, payload) ← tag json
  if constructor = "Move" then placeAnnotations ctx locals fuel payload
  else if constructor = "Copy" then
    let (place, _) ← pair payload
    placeAnnotations ctx locals fuel place
  else
    let (_, declared) ← pair (← field payload "Untagged")
    requireType (← type ctx none 64 declared) actual

def expressionAnnotations (ctx : Context) (locals : List Ty) (result : Ty)
    (fuel : Nat) (json : Json) : Read Unit := do
  let rhs ← SourceEval.Frontend.expression (localContext ctx locals) fuel json
  if !Types.checkExpr locals result rhs then throw "expression type constraints failed"
  let (constructor, payload) ← tag json
  if constructor = "Use" then
    let (op, _) ← pair payload
    operandAnnotations ctx locals fuel op
  else if constructor = "Ref" then
    placeAnnotations ctx locals fuel (← field payload "place")
    metadataAnnotations ctx locals (← field payload "ptr_metadata")
  else if constructor = "BinaryOp" then
    match ← array payload with
    | [_operator, left, right] =>
      operandAnnotations ctx locals fuel left
      operandAnnotations ctx locals fuel right
    | _ => throw "invalid binary operation annotations"
  else
    let (aggregate, args) ← pair payload
    let (_, payload) ← tag aggregate
    match ← array payload with
    | [reference, _, _] =>
      requireType (← type ctx none 64 (json% {"Untagged":{"Adt":$(reference)}})) result
      for op in ← array args do operandAnnotations ctx locals fuel op
    | _ => throw "invalid aggregate annotations"

def unwindAnnotations (ctx : Context) (locals : List Ty) (fuel : Nat) (json : Json) : Read Unit := do
  LookupSource.Frontend.unwindWith true (localContext ctx locals) json
  for statement in ← array (← field json "statements") do
    let kind ← field statement "kind"
    if let .obj _ := kind then
      let (constructor, payload) ← tag kind
      if constructor = "Drop" then placeAnnotations ctx locals fuel (← field payload "place")

def actionAnnotations (info : ProgramReader.ContextInfo) (ctx : Context) (locals : List Ty)
    (fuel : Nat) (constructor : String) (payload : Json) : Read Unit := do
  let action ← SourceEval.Frontend.action
    (fun index => required (info.functions.lookup index)) (fun index => info.drops.contains index)
    (localContext ctx locals) fuel constructor payload
  if !Types.checkAction locals action then throw "statement type constraints failed"
  if constructor = "Assign" then
    let (dest, rhs) ← pair payload
    placeAnnotations ctx locals fuel dest
    let slot ← localSlot (localContext ctx locals) dest
    expressionAnnotations ctx locals (← required locals[slot]?) fuel rhs
  else if constructor = "Drop" then
    placeAnnotations ctx locals fuel (← field payload "place")
    unwindAnnotations ctx locals fuel (← field payload "on_unwind")
  else if constructor = "Borrowck" then
    let (_, place) ← tag payload
    placeAnnotations ctx locals fuel place
  else if constructor = "Call" then
    placeAnnotations ctx locals fuel (← field payload "dest")
    unwindAnnotations ctx locals fuel (← field payload "on_unwind")
    let call ← field payload "call"
    for op in ← array (← field call "args") do operandAnnotations ctx locals fuel op
    let (_, regular) ← tag (← field call "func")
    let generics ← field regular "generics"
    emptyArrays generics ["const_generics", "trait_refs"]
    let genericTypes ← (← array (← field generics "types")).mapM (type ctx none 64)
    match action with
    | .call function args _ =>
      let expected ← if function = .boxNew then required (Types.inferOperands locals args) else pure []
      if !SourceTypes.sameList genericTypes expected then throw "callee generic instance mismatch"
    | _ => throw "call normalization mismatch"

def statementAnnotations (info : ProgramReader.ContextInfo) (ctx : Context) (locals : List Ty) :
    Nat → List Json → Read Unit
  | 0, _ => throw "statement annotation budget exceeded"
  | _ + 1, [] => pure ()
  | fuel + 1, statement :: rest => do
    let kind ← field statement "kind"
    if let .str label := kind then
      if label != "Return" && label != "UndefinedBehavior" then throw "unsupported terminal annotation"
      if !rest.isEmpty then throw "statements after terminal"
    else
      let (constructor, payload) ← tag kind
      if constructor = "Switch" then
        let data ← field payload "data"
        scrutineeAnnotations ctx locals fuel (← field data "scrutinee")
        for branch in ← array (← field data "branches") do
          let (literal, _) ← pair branch
          keyAnnotations ctx literal
        for branch in ← array (← field payload "branches") do
          statementAnnotations info ctx locals fuel (← array (← field branch "statements"))
      else actionAnnotations info ctx locals fuel constructor payload
      statementAnnotations info ctx locals fuel rest
termination_by structural fuel _ => fuel

end SubtreeProofs.Rust.SourceEval.TypeReader
