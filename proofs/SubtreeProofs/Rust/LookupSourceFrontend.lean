module

public import SubtreeProofs.Rust.LookupSourceControl
public import Lean.Data.Json.Elab

/-! An executable, kernel-reducible reader for the pinned non-deduplicated
Charon JSON lookup fragment. It validates crate/profile, declaration identity,
supported signatures, local bounds, thin shared borrows, normal-path syntax,
call identity/arity, binary routing and the allowed unwind profile. Unsupported
forms fail explicitly. Field typing, borrow regions and heap adequacy remain
outside this snapshot/control reader. JSON is data, not generated Lean code. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Frontend

open Lean

abbrev Read := Except String

def array (json : Json) : Read (List Json) := Array.toList <$> json.getArr?

def tag (json : Json) : Read (String × Json) := do
  match (← json.getObj?).toList with
  | [entry] => pure entry
  | _ => throw "expected exactly one constructor tag"

def field (json : Json) (key : String) : Read Json := json.getObjVal? key

def pair (json : Json) : Read (Json × Json) := do
  match ← array json with
  | [first, second] => pure (first, second)
  | _ => throw "expected a pair"

def optionalNat (json : Json) : Read (Option Nat) :=
  if json.isNull then pure none else some <$> json.getNat?

def ident (json : Json) (expected : String) : Read Bool := do
  let (constructor, payload) ← tag json
  if constructor != "Ident" then return false
  let (pathName, disambiguator) ← pair payload
  pure ((← pathName.getStr?) = expected && (← disambiguator.getNat?) = 0)

structure Context where
  kinds : List (Nat × Kind)
  functions : List (Nat × Function)
  localCount : Nat := 0

def kindRef (ctx : Context) (json : Json) : Read Kind := do
  let index ← (← field json "id").getNat?
  match ctx.kinds.lookup index with
  | some kind => pure kind
  | none => throw "unsupported type declaration identity"

def slot (ctx : Context) (json : Json) : Read Nat := do
  let index ← json.getNat?
  if index < ctx.localCount then pure index else throw "local slot out of bounds"

def place (ctx : Context) : Nat → Json → Read Place
  | 0, _ => throw "place nesting budget exceeded"
  | fuel + 1, json => do
    let (constructor, payload) ← tag (← field json "kind")
    if constructor = "Local" then return .local (← slot ctx payload)
    if constructor != "Projection" then throw "unsupported place"
    let (parent, projection) ← pair payload
    let parent ← place ctx fuel parent
    match projection with
    | .str "Deref" => pure (.deref parent)
    | _ =>
      let (constructor, payload) ← tag projection
      if constructor != "Field" then throw "unsupported projection"
      let (variant, index) ← pair payload
      pure (.field parent (← optionalNat variant) (← index.getNat?))

termination_by structural fuel _ => fuel

def localSlot (ctx : Context) (json : Json) : Read Nat := do
  let (constructor, payload) ← tag (← field json "kind")
  if constructor = "Local" then slot ctx payload else throw "whole local required"

def boolLiteral (json : Json) : Read Bool := do
  let (constructor, payload) ← tag json
  if constructor = "Bool" then payload.getBool? else throw "boolean literal required"

def operand (ctx : Context) (fuel : Nat) (json : Json) : Read Operand := do
  let (constructor, payload) ← tag json
  if constructor = "Move" then return .move (← localSlot ctx payload)
  if constructor = "Copy" then
    let (source, _trait) ← pair payload
    return .copy (← place ctx fuel source)
  if constructor = "Const" then
    let (literal, _type) ← pair (← field payload "Untagged")
    return .boolean (← boolLiteral literal)
  throw "unsupported operand"

def operands (ctx : Context) (fuel : Nat) (json : Json) : Read (List Operand) := do
  (← array json).mapM (operand ctx fuel)

def thinMetadata (ctx : Context) (json : Json) : Read Unit := do
  let (constructor, payload) ← tag json
  if constructor != "Const" then throw "constant thin metadata required"
  let (literal, type) ← pair (← field payload "Untagged")
  let (constructor, payload) ← tag literal
  if constructor != "Adt" then throw "unit metadata required"
  let (variant, fields) ← pair payload
  if !variant.isNull || !(← array fields).isEmpty then throw "non-unit pointer metadata"
  let (constructor, payload) ← tag (← field type "Untagged")
  if constructor != "Adt" || (← kindRef ctx payload) != .tuple then throw "unit metadata type required"

def rvalue (ctx : Context) (fuel : Nat) (json : Json) : Read RValue := do
  let (constructor, payload) ← tag json
  if constructor = "Use" then
    let (source, marker) ← pair payload
    if (← marker.getStr?) != "Yes" then throw "unsupported Use retag marker"
    return .use (← operand ctx fuel source)
  if constructor = "Ref" then
    if (← (← field payload "kind").getStr?) != "Shared" then throw "shared references only"
    thinMetadata ctx (← field payload "ptr_metadata")
    return .address (← place ctx fuel (← field payload "place"))
  if constructor = "Aggregate" then
    let (aggregate, values) ← pair payload
    let (constructor, payload) ← tag aggregate
    if constructor != "Adt" then throw "ADT aggregate required"
    match ← array payload with
    | [reference, variant, unionField] =>
      if !unionField.isNull then throw "union initialization unsupported"
      return .aggregate (← kindRef ctx reference) ((← optionalNat variant).getD 0)
        (← operands ctx fuel values)
    | _ => throw "invalid aggregate descriptor"
  throw "unsupported rvalue"

def key (ctx : Context) (json : Json) : Read Key := do
  let (literal, _type) ← pair (← field json "Untagged")
  let (constructor, payload) ← tag literal
  if constructor = "Bool" then return .boolean (← payload.getBool?)
  if constructor = "Discriminant" then
    let (reference, variant) ← pair payload
    return .variant (← kindRef ctx reference) (← variant.getNat?)
  throw "unsupported switch key"

def scrutinee (ctx : Context) (fuel : Nat) (json : Json) : Read Scrutinee := do
  let (constructor, payload) ← tag json
  if constructor = "Discriminant" then return .discriminant (← place ctx fuel payload)
  if constructor = "Value" then return .value (← operand ctx fuel payload)
  throw "unsupported switch scrutinee"

def caseEntry (ctx : Context) (json : Json) : Read (Key × Nat) := do
  let (literal, index) ← pair json
  pure (← key ctx literal, ← index.getNat?)

def arity : Function → Nat
  | .copyWord | .copyResult | .boxNew => 1
  | .compare => 2
  | .lookup => 3

def unwind (ctx : Context) (json : Json) : Read Unit := do
  for statement in ← array (← field json "statements") do
    let kind ← field statement "kind"
    match kind with
    | .str "UnwindResume" => pure ()
    | _ =>
      let (constructor, payload) ← tag kind
      if constructor = "StorageDead" then
        let _ ← slot ctx payload
      else if constructor = "Drop" then
        if (← (← field payload "kind").getStr?) != "Conditional" then throw "precise unwind drop unsupported"
        let _ ← localSlot ctx (← field payload "place")
      else throw "nontrivial unwind unsupported"

def actionWith {F : Type} (resolve : Nat → Read F) (callArity : F → Nat)
    (ctx : Context) (fuel : Nat) (constructor : String) (payload : Json) : Read (Control.Action F) := do
  if constructor = "StorageLive" then return .storageLive (← slot ctx payload)
  if constructor = "StorageDead" then return .storageDead (← slot ctx payload)
  if constructor = "Assign" then
    let (dest, rhs) ← pair payload
    return .assign (← localSlot ctx dest) (← rvalue ctx fuel rhs)
  if constructor = "Call" then
    let dest ← localSlot ctx (← field payload "dest")
    unwind ctx (← field payload "on_unwind")
    let call ← field payload "call"
    if (← (← field call "safety").getStr?) != "Inherit" then throw "explicit unsafe call unsupported"
    let (constructor, payload) ← tag (← field call "func")
    if constructor != "Regular" then throw "nonregular call unsupported"
    let (constructor, payload) ← tag (← field payload "kind")
    if constructor != "Fun" then throw "indirect/trait call unsupported"
    let index ← payload.getNat?
    let function ← resolve index
    let args ← operands ctx fuel (← field call "args")
    if args.length != callArity function then throw "wrong call arity"
    return .call function args dest
  if constructor = "Drop" then
    if (← (← field payload "kind").getStr?) != "Conditional" then throw "live/precise drop unsupported"
    return .dropConditional (← localSlot ctx (← field payload "place"))
  throw "unsupported source statement"

def action (ctx : Context) : Nat → String → Json → Read Control.Action :=
  actionWith (fun index => match ctx.functions.lookup index with
    | some function => pure function
    | none => throw "unsupported callee identity") arity ctx

def sequenceWith {F : Type} (parseAction : Context → Nat → String → Json → Read (Control.Action F))
    (ctx : Context) : Nat → List Json → Read (Control.Block F)
  | 0, _ => throw "statement nesting budget exceeded"
  | _ + 1, [] => pure .done
  | fuel + 1, statement :: rest => do
    let kind ← field statement "kind"
    match kind with
    | .str "Return" =>
      if rest.isEmpty then pure .ret else throw "statements after unconditional return"
    | _ =>
      let (constructor, payload) ← tag kind
      if constructor = "Switch" then
        let data ← field payload "data"
        let cases ← (← array (← field data "branches")).mapM (caseEntry ctx)
        let fallback ← optionalNat (← field data "fallback")
        if (Control.lowerDispatch cases fallback).isNone then throw "unsupported binary routing"
        match ← array (← field payload "branches") with
        | [zero, one] =>
          return .switch (← scrutinee ctx fuel (← field data "scrutinee")) cases fallback
            (← sequenceWith parseAction ctx fuel (← array (← field zero "statements")))
            (← sequenceWith parseAction ctx fuel (← array (← field one "statements")))
            (← sequenceWith parseAction ctx fuel rest)
        | _ => throw "exactly two source arms required"
      else return .step (← parseAction ctx fuel constructor payload) (← sequenceWith parseAction ctx fuel rest)

termination_by structural fuel _ => fuel

def sequence (ctx : Context) : Nat → List Json → Read Control.Block := sequenceWith action ctx

def kindName (pathName : List Json) : Read (Option Kind) := do
  match pathName with
  | [root, last] =>
    if ← ident root "verified_ordered_core" then
      for (label, kind) in [("BalancedWord", Kind.word), ("MemoTable", .table),
          ("MemoEntry", .entry), ("CommonEmbedding", .embedding)] do
        if ← ident last label then return some kind
    pure none
  | [root, module, last] =>
    if (← ident root "core") && (← ident module "option") && (← ident last "Option") then
      pure (some .optional)
    else pure none
  | [builtin] =>
    let (constructor, payload) ← tag builtin
    if constructor != "Builtin" then return none
    let (builtin, disambiguator) ← pair payload
    let (constructor, index) ← tag builtin
    if constructor = "Tuple" && (← index.getNat?) = 0 && (← disambiguator.getNat?) = 0 then
      pure (some .tuple)
    else pure none
  | _ => pure none

def rootName (pathName : List Json) : Read (Option Function) := do
  match pathName with
  | [root, last] =>
    if ← ident root "verified_ordered_core" then
      for (label, function) in [("copy_word", Function.copyWord), ("words_equal", .compare),
          ("copy_result", .copyResult), ("memo_lookup", .lookup)] do
        if ← ident last label then return some function
    pure none
  | _ => pure none

def boxName (pathName : List Json) : Read Bool := do
  match pathName with
  | [root, module, implementation, last] =>
    if !(← ident root "alloc") || !(← ident module "boxed") || !(← ident last "new") then return false
    let type ← field (← field implementation "Impl") "Ty"
    if (← (← field type "kind").getStr?) != "InherentImplBlock" then return false
    let adt ← field (← field (← field type "skip_binder") "Untagged") "Adt"
    pure ((← (← field adt "builtin").getStr?) = "Box")
  | _ => pure false

def typeKind (ctx : Context) (type : Json) : Read Kind := do
  let (constructor, payload) ← tag (← field type "Untagged")
  if constructor != "Adt" then throw "named ADT type required"
  kindRef ctx payload

def sharedInput (ctx : Context) (type : Json) (expected : Kind) : Read Unit := do
  let (constructor, payload) ← tag (← field type "Untagged")
  if constructor != "Ref" then throw "shared input reference required"
  match ← array payload with
  | [_region, pointee, mutability] =>
    if (← mutability.getStr?) != "Shared" || (← typeKind ctx pointee) != expected then
      throw "unsupported input type"
  | _ => throw "invalid reference descriptor"

def signature (ctx : Context) (function : Function) (decl : Json) : Read Unit := do
  let signature ← field decl "signature"
  let inputs ← array (← field signature "inputs")
  let expected := match function with
    | .copyWord | .copyResult => [if function = .copyWord then Kind.word else .embedding]
    | .compare => [.word, .word]
    | .lookup => [.table, .word, .word]
    | .boxNew => []
  if inputs.length != expected.length then throw "unsupported signature arity"
  for (input, kind) in inputs.zip expected do sharedInput ctx input kind
  let output ← field signature "output"
  if function = .compare then
    let (constructor, payload) ← tag (← field output "Untagged")
    if constructor != "Scalar" || (← payload.getStr?) != "Bool" then throw "boolean output required"
  else
    let expected := if function = .copyWord then Kind.word else if function = .copyResult then .embedding else .optional
    if (← typeKind ctx output) != expected then throw "unsupported output type"
    if function = .lookup then
      let adt ← field (← field output "Untagged") "Adt"
      match ← array (← field (← field adt "generics") "types") with
      | [inner] => if (← typeKind ctx inner) != .embedding then throw "embedding option output required"
      | _ => throw "single option type argument required"

def declarations (json : Json) : Read (List Json) := do
  let decls := (← array json).filter fun decl => !decl.isNull
  let ids ← decls.mapM fun decl => do (← field decl "def_id").getNat?
  if !(decide ids.Nodup) then throw "duplicate declaration identity"
  pure decls

def context (crate : Json) : Read (Context × List (Function × Json)) := do
  let mut kinds := []
  for decl in ← declarations (← field crate "type_decls") do
    let pathName ← array (← field (← field decl "item_meta") "name")
    if let some kind ← kindName pathName then
      kinds := kinds ++ [(← (← field decl "def_id").getNat?, kind)]
  if !(decide (kinds.map Prod.snd).Nodup) then throw "duplicate supported type identity"
  let mut functions := []
  let mut roots := []
  for decl in ← declarations (← field crate "fun_decls") do
    let pathName ← array (← field (← field decl "item_meta") "name")
    let index ← (← field decl "def_id").getNat?
    if let some function ← rootName pathName then
      functions := functions ++ [(index, function)]
      roots := roots ++ [(function, decl)]
    else if ← boxName pathName then functions := functions ++ [(index, .boxNew)]
  if !(decide (functions.map Prod.snd).Nodup) then throw "duplicate supported function identity"
  pure (⟨kinds, functions, 0⟩, roots)

structure Program where
  copyWord : Control.Block
  compare : Control.Block
  copyResult : Control.Block
  lookup : Control.Block

def Program.body (program : Program) : Function → Control.Block
  | .copyWord => program.copyWord
  | .compare => program.compare
  | .copyResult => program.copyResult
  | .lookup => program.lookup
  | .boxNew => .done

def function (ctx : Context) (roots : List (Function × Json)) (fuel : Nat) (pathName : Function) : Read Control.Block := do
  let decl ← match roots.lookup pathName with
    | some decl => pure decl
    | none => throw "required root helper missing"
  signature ctx pathName decl
  let body ← field (← field decl "body") "Structured"
  let locals ← field body "locals"
  if (← (← field locals "arg_count").getNat?) != arity pathName then throw "body argument count mismatch"
  let slots ← array (← field locals "locals")
  if slots.length ≤ arity pathName then throw "incomplete local declarations"
  let indices ← slots.mapM fun decl => do (← field decl "index").getNat?
  if indices != List.range slots.length then throw "noncanonical local declaration indices"
  sequence { ctx with localCount := slots.length } fuel (← array (← field (← field body "body") "statements"))

def read (json : Json) (fuel : Nat) : Read Program := do
  if (← (← field json "charon_version").getStr?) != "0.1.315" then throw "unsupported Charon version"
  if (← (← field json "has_errors").getBool?) then throw "Charon extraction contains errors"
  let crate ← field json "translated"
  if (← (← field crate "crate_name").getStr?) != "verified_ordered_core" then throw "wrong crate identity"
  let options ← field crate "options"
  if !(← (← field options "no_dedup_serialized_ast").getBool?) then throw "deduplicated AST unsupported"
  if (← (← field options "preset").getStr?) != "Aeneas" then throw "wrong extraction profile"
  let (ctx, roots) ← context crate
  pure ⟨← function ctx roots fuel .copyWord, ← function ctx roots fuel .compare,
    ← function ctx roots fuel .copyResult, ← function ctx roots fuel .lookup⟩

def functions : List Function := [.copyWord, .compare, .copyResult, .lookup, .boxNew]

/-- Check a proposed normalization against the retained source declarations.
The kernel can evaluate this Boolean without trusting an external reifier. -/
def check (json : Json) (fuel : Nat) (body : Function → Code) : Bool :=
  match read json fuel with
  | .error _ => false
  | .ok program => functions.all fun function =>
      decide (Control.lower (program.body function) = some (body function))

theorem check_iff (json : Json) (fuel : Nat) (body : Function → Code) :
    check json fuel body = true ↔
      ∃ program, read json fuel = .ok program ∧
        ∀ function, Control.lower (program.body function) = some (body function) := by
  cases hr : read json fuel with
  | error message => simp [check, hr]
  | ok program =>
    simp only [check, hr]
    constructor
    · intro hc
      refine ⟨program, rfl, ?_⟩
      intro function
      have hm : function ∈ functions := by cases function <;> simp [functions]
      exact of_decide_eq_true (List.all_eq_true.mp hc function hm)
    · rintro ⟨same, he, hl⟩
      cases he
      exact List.all_eq_true.mpr fun function _ => by simp [hl function]

/-- A successful check certifies exact source-control execution/cost equality
for every call and fuel in the declared primitive/snapshot semantics. -/
theorem checked_run (json : Json) (parseFuel : Nat) (body : Function → Code)
    (hc : check json parseFuel body = true) :
    ∃ program, read json parseFuel = .ok program ∧
      ∀ fuel function args, Control.run program.body fuel function args =
        LookupSource.run body fuel function args := by
  obtain ⟨program, hr, hl⟩ := (check_iff json parseFuel body).mp hc
  exact ⟨program, hr, Control.run_lower program.body body hl⟩

end SubtreeProofs.Rust.LookupSource.Frontend
