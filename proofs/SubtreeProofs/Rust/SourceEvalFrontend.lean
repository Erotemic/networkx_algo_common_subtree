module

public import SubtreeProofs.Rust.SourceEvalMachine
public import SubtreeProofs.Rust.LookupSourceFrontend

/-! Evaluator expression/action decoding through the shared source frontend.
The enclosing program must supply checked function/drop identities and local
bounds. This is not yet a certificate for an entire extracted evaluator. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Frontend

open Lean LookupSource
open LookupSource.Frontend hiding operand operands rvalue action sequence arity

def unsigned32 (json : Json) : Read Unit := do
  let (constructor, payload) ← tag (← field json "Untagged")
  if constructor != "Scalar" then throw "u32 scalar type required"
  let (constructor, payload) ← tag payload
  if constructor != "Integer" then throw "integer type required"
  let (constructor, payload) ← tag payload
  if constructor != "Unsigned" || (← payload.getStr?) != "U32" then throw "u32 type required"

def literal (value type : Json) : Read Operand := do
  let (constructor, payload) ← tag value
  if constructor = "Bool" then
    let (constructor, payloadType) ← tag (← field type "Untagged")
    if constructor != "Scalar" || (← payloadType.getStr?) != "Bool" then throw "boolean literal type mismatch"
    return .boolean (← payload.getBool?)
  if constructor != "Integer" then throw "unsupported evaluator literal"
  unsigned32 type
  let (constructor, payload) ← tag payload
  if constructor != "Unsigned" then throw "unsigned literal required"
  let (kind, digits) ← pair payload
  if (← kind.getStr?) != "U32" then throw "u32 literal required"
  let value ← unsignedDecimal (← digits.getStr?)
  if value < 2^32 then return .number value else throw "u32 literal out of range"

def operand (ctx : Context) (fuel : Nat) (json : Json) : Read Operand :=
  operandWith (fun ctx fuel json => Operand.move <$> place ctx fuel json) Operand.copy literal ctx fuel json

def operands (ctx : Context) (fuel : Nat) (json : Json) : Read (List Operand) := do
  (← array json).mapM (operand ctx fuel)

def extraExpr (ctx : Context) (fuel : Nat) (constructor : String) (payload : Json) : Read Expr := do
  if constructor != "BinaryOp" then throw "unsupported evaluator expression"
  match ← array payload with
  | [operator, left, right] =>
    if (← operator.getStr?) != "Lt" then throw "only scalar less-than supported"
    return .less (← operand ctx fuel left) (← operand ctx fuel right)
  | _ => throw "invalid binary operation"

def expression (ctx : Context) (fuel : Nat) (json : Json) : Read Expr :=
  rvalueWith operand Expr.use Expr.address Expr.aggregate extraExpr ctx fuel json

def action (resolve : Nat → Read Function) (dropAllowed : Nat → Bool)
    (ctx : Context) (fuel : Nat) (constructor : String) (payload : Json) : Read Action := do
  if constructor = "StorageLive" then return .storageLive (← slot ctx payload)
  if constructor = "StorageDead" then return .storageDead (← slot ctx payload)
  if constructor = "Assign" then
    let (dest, rhs) ← pair payload
    return .assign (← localSlot ctx dest) (← expression ctx fuel rhs)
  if constructor = "Call" then
    let (function, args, dest) ← callWith resolve arity operands (unwindWith true) ctx fuel payload
    return .call function args dest
  if constructor = "Drop" then
    if (← (← field payload "kind").getStr?) != "Conditional" then throw "precise drop unsupported"
    let (constructor, function) ← tag (← field (← field payload "fn_ptr") "kind")
    if constructor != "Fun" || !(dropAllowed (← function.getNat?)) then throw "unsupported destructor identity"
    unwindWith true ctx (← field payload "on_unwind")
    return .drop (← localSlot ctx (← field payload "place"))
  if constructor = "Borrowck" then
    let (constructor, placeJson) ← tag payload
    if constructor != "FakeRead" then throw "unsupported borrow-check metadata"
    return .fakeRead (← place ctx fuel placeJson)
  throw "unsupported evaluator action"

def sequence (resolve : Nat → Read Function) (dropAllowed : Nat → Bool) (ctx : Context)
    (fuel : Nat) (statements : List Json) : Read Code :=
  sequenceWithActions (action resolve dropAllowed) (fun label =>
    if label = "Return" then pure .ret
    else if label = "UndefinedBehavior" then pure (.step .undefinedBehavior .done)
    else throw "unsupported evaluator terminal") ctx fuel statements

end SubtreeProofs.Rust.SourceEval.Frontend
