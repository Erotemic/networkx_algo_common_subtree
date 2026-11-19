module

public import SubtreeProofs.Rust.LookupTypeReader

/-! Cross-check all normal-body place, operand, aggregate and call type
annotations against declared local types and the independent field rules.
Unwind drop-place annotations are read too; unwind execution remains outside
the supported semantics. Region identities are deliberately lifetime-erased. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.TypeReader

open Lean Heap Frontend SourceTypes

def required {α : Type} (value : Option α) : Read α :=
  match value with | some value => pure value | none => throw "ill-typed normalized expression"

def parameterType (json : Json) : Read Unit := do
  let (constructor, payload) ← tag (← field json "Untagged")
  if constructor != "TypeVar" then throw "Box signature must use its parameter"
  let (constructor, payload) ← tag payload
  if constructor != "Free" || (← payload.getNat?) != 0 then throw "wrong Box signature parameter"

def boxInstance (ctx : Context) (json : Json) : Read Unit := do
  let reference ← field (← field json "Untagged") "Adt"
  if (← (← field reference "id").getNat?) != ctx.boxId ||
      (← (← field reference "builtin").getStr?) != "Box" then throw "wrong Box signature identity"
  let generics ← field reference "generics"
  emptyArrays generics ["regions", "const_generics", "trait_refs"]
  match ← array (← field generics "types") with
  | [inner] => parameterType inner
  | _ => throw "Box signature requires one parameter"

def boxMethod (ctx : Context) (crate : Json) : Read Unit := do
  let index ← required (ctx.source.functions.findSome? fun (index, function) =>
    if function = .boxNew then some index else none)
  let decls ← declarations (← field crate "fun_decls")
  let ids ← decls.mapM fun decl => do (← field decl "def_id").getNat?
  let decl ← required ((ids.zip decls).lookup index)
  genericParams (← field decl "generics") 1
  let signature ← field decl "signature"
  if (← (← field signature "is_unsafe").getBool?) || (← (← field signature "is_variadic").getBool?) ||
      (← (← field signature "abi").getStr?) != "Rust" then throw "unsupported Box ABI"
  match ← array (← field signature "inputs") with
  | [inner] => parameterType inner
  | _ => throw "Box constructor signature arity"
  boxInstance ctx (← field signature "output")
  boxInstance ctx (← field (← field decl "src") "InherentImpl" >>= fun source => field source "self_ty")
  if (← (← field decl "body").getStr?) != "Opaque" then throw "Box constructor must be primitive opaque"

def localContext (ctx : Context) (locals : List Ty) : Frontend.Context :=
  { ctx.source with localCount := locals.length }

def placeAnnotations (ctx : Context) (locals : List Ty) : Nat → Json → Read Unit
  | 0, _ => throw "place annotation budget exceeded"
  | fuel + 1, json => do
    let place ← Frontend.place (localContext ctx locals) (fuel + 1) json
    let actual ← required (inferPlace locals place)
    requireType (← type ctx none 64 (← field json "ty")) actual
    let (constructor, payload) ← tag (← field json "kind")
    if constructor = "Projection" then
      let (parent, _) ← pair payload
      placeAnnotations ctx locals fuel parent
termination_by structural fuel _ => fuel

def operandAnnotations (ctx : Context) (locals : List Ty) (fuel : Nat) (json : Json) : Read Unit := do
  let op ← Frontend.operand (localContext ctx locals) fuel json
  let _ ← required (inferOperand locals op)
  let (constructor, payload) ← tag json
  if constructor = "Move" then placeAnnotations ctx locals fuel payload
  else if constructor = "Copy" then
    let (place, _) ← pair payload
    placeAnnotations ctx locals fuel place
  else
    let (_, declared) ← pair (← field payload "Untagged")
    requireType (← type ctx none 64 declared) .boolean

def metadataAnnotations (ctx : Context) (locals : List Ty) (json : Json) : Read Unit := do
  thinMetadata (localContext ctx locals) json
  let (_, payload) ← tag json
  let (_, declared) ← pair (← field payload "Untagged")
  requireType (← type ctx none 64 declared) (.tuple [])

def rvalueAnnotations (ctx : Context) (locals : List Ty) (fuel : Nat) (json : Json) : Read Unit := do
  let rhs ← Frontend.rvalue (localContext ctx locals) fuel json
  let actual ← required (inferRValue locals rhs)
  let (constructor, payload) ← tag json
  if constructor = "Use" then
    let (op, _) ← pair payload
    operandAnnotations ctx locals fuel op
  else if constructor = "Ref" then
    placeAnnotations ctx locals fuel (← field payload "place")
    metadataAnnotations ctx locals (← field payload "ptr_metadata")
  else
    let (aggregate, args) ← pair payload
    let (_, payload) ← tag aggregate
    match ← array payload with
    | [reference, _, _] =>
      requireType (← type ctx none 64 (json% {"Untagged":{"Adt":$(reference)}})) actual
      for op in ← array args do operandAnnotations ctx locals fuel op
    | _ => throw "invalid aggregate metadata"

def unwindAnnotations (ctx : Context) (locals : List Ty) (fuel : Nat) (json : Json) : Read Unit := do
  Frontend.unwind (localContext ctx locals) json
  for statement in ← array (← field json "statements") do
    let kind ← field statement "kind"
    if let .obj _ := kind then
      let (constructor, payload) ← tag kind
      if constructor = "Drop" then placeAnnotations ctx locals fuel (← field payload "place")

def actionAnnotationsWith {F : Type}
    (parseAction : Frontend.Context → Nat → String → Json → Read (Control.Action F))
    (calleeOutput : F → List Ty → Option Ty) (isBox : F → Bool)
    (ctx : Context) (locals : List Ty) (fuel : Nat) (constructor : String) (payload : Json) : Read Unit := do
  let action ← parseAction (localContext ctx locals) fuel constructor payload
  if !checkActionWith calleeOutput locals action.lower then throw "statement disagrees with declared local types"
  if constructor = "Assign" then
    let (dest, rhs) ← pair payload
    placeAnnotations ctx locals fuel dest
    rvalueAnnotations ctx locals fuel rhs
  else if constructor = "Drop" then placeAnnotations ctx locals fuel (← field payload "place")
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
      let expected ← if isBox function then required (inferOperands locals args) else pure []
      if !sameList genericTypes expected then throw "callee generic instance mismatch"
    | _ => throw "call normalization mismatch"

def scrutineeAnnotations (ctx : Context) (locals : List Ty) (fuel : Nat) (json : Json) : Read Unit := do
  let (constructor, payload) ← tag json
  if constructor = "Value" then operandAnnotations ctx locals fuel payload
  else if constructor = "Discriminant" then placeAnnotations ctx locals fuel payload
  else throw "unsupported scrutinee annotation"

def keyAnnotations (ctx : Context) (json : Json) : Read Unit := do
  let (literal, declared) ← pair (← field json "Untagged")
  let (constructor, payload) ← tag literal
  if constructor = "Bool" then requireType (← type ctx none 64 declared) .boolean
  else if constructor = "Discriminant" then
    let (reference, _) ← pair payload
    let _ ← type ctx none 64 (json% {"Untagged":{"Adt":$(reference)}})
    let scalar ← field (← field declared "Untagged") "Scalar"
    let (tag, payload) ← Frontend.tag (← field scalar "Integer")
    if tag != "Signed" || (← payload.getStr?) != "Isize" then throw "discriminant must have isize annotation"
  else throw "unsupported switch constant annotation"

def actionAnnotations (ctx : Context) (locals : List Ty) : Nat → String → Json → Read Unit :=
  actionAnnotationsWith Frontend.action callOutput (fun function => decide (function = .boxNew)) ctx locals

def statementAnnotationsWith {F : Type}
    (parseAction : Frontend.Context → Nat → String → Json → Read (Control.Action F))
    (calleeOutput : F → List Ty → Option Ty) (isBox : F → Bool)
    (ctx : Context) (locals : List Ty) : Nat → List Json → Read Unit
  | 0, _ => throw "statement annotation budget exceeded"
  | _ + 1, [] => pure ()
  | fuel + 1, statement :: rest => do
    let kind ← field statement "kind"
    if let .str "Return" := kind then
      if !rest.isEmpty then throw "statements after return"
    else
      let (constructor, payload) ← tag kind
      if constructor = "Switch" then
        let data ← field payload "data"
        scrutineeAnnotations ctx locals fuel (← field data "scrutinee")
        for branch in ← array (← field data "branches") do
          let (literal, _) ← pair branch
          keyAnnotations ctx literal
        for branch in ← array (← field payload "branches") do
          statementAnnotationsWith parseAction calleeOutput isBox ctx locals fuel (← array (← field branch "statements"))
      else actionAnnotationsWith parseAction calleeOutput isBox ctx locals fuel constructor payload
      statementAnnotationsWith parseAction calleeOutput isBox ctx locals fuel rest
termination_by structural fuel _ => fuel

def statementAnnotations (ctx : Context) (locals : List Ty) : Nat → List Json → Read Unit :=
  statementAnnotationsWith Frontend.action callOutput (fun function => decide (function = .boxNew)) ctx locals

structure Definition where
  function : Function
  locals : List Ty
  code : Code
  boundary : locals.take ((inputs function).length + 1) = output function :: inputs function
  constraints : CodeConstraints locals (output function) code

def definition (ctx : Context) (roots : List (Function × Json)) (fuel : Nat) (function : Function) :
    Read Definition := do
  let decl ← required (roots.lookup function)
  let generics ← field decl "generics"
  emptyArrays generics ["types", "const_generics", "trait_clauses", "outlives", "trait_type_constraints"]
  let signature ← field decl "signature"
  if (← (← field signature "is_unsafe").getBool?) || (← (← field signature "is_variadic").getBool?) then
    throw "unsafe/variadic helper signature"
  if (← (← field signature "abi").getStr?) != "Rust" then throw "Rust ABI required"
  let parameters ← (← array (← field signature "inputs")).mapM (type ctx none 64)
  if !sameList parameters (inputs function) then throw "helper parameter types mismatch"
  requireType (← type ctx none 64 (← field signature "output")) (output function)
  let body ← field (← field decl "body") "Structured"
  let slots ← array (← field (← field body "locals") "locals")
  let locals ← slots.mapM fun slot => do type ctx none 64 (← field slot "ty")
  if hb : sameList (locals.take ((inputs function).length + 1)) (output function :: inputs function) = true then
    let source ← Frontend.function ctx.source roots fuel function
    let code ← required (Control.lower source)
    statementAnnotations ctx locals fuel (← array (← field (← field body "body") "statements"))
    if hc : checkCode locals (output function) code = true then
      pure ⟨function, locals, code, sameList_eq hb, checkCode_sound hc⟩
    else throw "normalized code type constraints failed"
  else throw "return/argument local type mismatch"

structure Program where
  layouts : List Layout
  layouts_sound : ∀ layout ∈ layouts, Shape layout.kind layout.variant layout.fields (.adt layout.kind)
  definitions : List Definition
  covers : definitions.map Definition.function = [.copyWord, .compare, .copyResult, .lookup]

def read (json : Json) (fuel : Nat) : Read Program := do
  let _ ← Frontend.read json fuel
  let crate ← field json "translated"
  let (source, roots) ← Frontend.context crate
  let ctx ← makeContext crate source
  boxMethod ctx crate
  let shapes ← layouts ctx crate
  let defs ← [Function.copyWord, .compare, .copyResult, .lookup].mapM (definition ctx roots fuel)
  if hs : shapes.all layoutCheck = true then
    if hd : defs.map Definition.function = [.copyWord, .compare, .copyResult, .lookup] then
      pure ⟨shapes, fun layout hl => layoutCheck_sound (List.all_eq_true.mp hs layout hl), defs, hd⟩
    else throw "ordinary helper coverage mismatch"
  else throw "layout proof check failed"

def check (json : Json) (fuel : Nat) (body : Function → Code) : Bool :=
  match read json fuel with
  | .error _ => false
  | .ok program => program.definitions.all fun decl => decide (decl.code = body decl.function)

theorem check_sound {json : Json} {fuel : Nat} {body : Function → Code} (h : check json fuel body = true) :
    ∃ program, read json fuel = .ok program ∧
      (∀ layout ∈ program.layouts, Shape layout.kind layout.variant layout.fields (.adt layout.kind)) ∧
      ∀ decl ∈ program.definitions, CodeConstraints decl.locals (output decl.function) (body decl.function) := by
  cases hr : read json fuel with
  | error message => simp [check, hr] at h
  | ok program =>
    refine ⟨program, rfl, program.layouts_sound, ?_⟩
    intro decl hd
    have he : decl.code = body decl.function := of_decide_eq_true
      (List.all_eq_true.mp (by simpa only [check, hr] using h) decl hd)
    simpa only [← he] using decl.constraints

theorem check_functions {json : Json} {fuel : Nat} {body : Function → Code}
    (h : check json fuel body = true) (function : Function) (hf : function ≠ .boxNew) :
    ∃ locals, CodeConstraints locals (output function) (body function) := by
  obtain ⟨program, _, _, ht⟩ := check_sound h
  have hm : function ∈ program.definitions.map Definition.function := by
    rw [program.covers]
    cases function <;> simp_all
  obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
  have hc := ht decl hd
  rw [he] at hc
  exact ⟨decl.locals, hc⟩

theorem check_boundaries {json : Json} {fuel : Nat} {body : Function → Code}
    (h : check json fuel body = true) (function : Function) (hf : function ≠ .boxNew) :
    ∃ locals, locals.take ((inputs function).length + 1) = output function :: inputs function ∧
      CodeConstraints locals (output function) (body function) := by
  obtain ⟨program, _, _, ht⟩ := check_sound h
  have hm : function ∈ program.definitions.map Definition.function := by
    rw [program.covers]
    cases function <;> simp_all
  obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
  have hc := ht decl hd
  have hb := decl.boundary
  rw [he] at hc hb
  exact ⟨decl.locals, hb, hc⟩

end SubtreeProofs.Rust.LookupSource.TypeReader
