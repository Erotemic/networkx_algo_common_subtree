module

public import SubtreeProofs.Rust.SourceEvalFrontend
public import SubtreeProofs.Rust.MemoSourceFrontend
public import SubtreeProofs.Rust.LookupTypeAnnotations

/-! Whole-program source reading for the evaluator and public core. Function
and destructor identities, signatures, ABI, local bounds and complete helper
coverage are checked. Static local/field typing and addressed safety remain
subsequent obligations. The code is the retained source-control tree itself. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.ProgramReader

open Lean LookupSource
open LookupSource.Frontend hiding Context Program function read signature rootName context operand operands action sequence arity

abbrev Context := LookupSource.Frontend.Context

def names : List (String × SourceEval.Function) :=
  [("copy_word", .copyWord), ("words_equal", .compare), ("copy_result", .copyResult),
   ("memo_lookup", .lookup), ("concatenate", .concatenate), ("memo_insert", .insert),
   ("choose_longer", .chooseLonger), ("memoized_common_embedding", .evaluate),
   ("maximum_common_embedding", .maximum)]

def helpers : List SourceEval.Function := names.map Prod.snd

def rootName (path : List Json) : Read (Option SourceEval.Function) := do
  match path with
  | [root, last] =>
    if ← ident root "verified_ordered_core" then
      for (label, function) in names do
        if ← ident last label then return some function
    pure none
  | _ => pure none

def checkedAddName (path : List Json) : Read Bool := do
  match path with
  | [root, module, implementation, last] =>
    if !(← ident root "core") || !(← ident module "num") || !(← ident last "checked_add") then return false
    let type ← field (← field implementation "Impl") "Ty"
    if (← (← field type "kind").getStr?) != "InherentImplBlock" then return false
    SourceEval.Frontend.unsigned32 (← field type "skip_binder")
    pure true
  | _ => pure false

def dropName (path : List Json) : Read Bool := do
  let last ← LookupSource.TypeReader.required path.getLast?
  let (constructor, payload) ← tag last
  if constructor != "Builtin" then return false
  let (label, index) ← pair payload
  if (← label.getStr?) != "DropGlue" || (← index.getNat?) != 0 then return false
  match path with
  | [root, type, implementation, _] =>
    let (constructor, _) ← tag (← field implementation "Impl")
    if constructor != "Trait" || !(← ident root "verified_ordered_core") then return false
    for label in ["BalancedWord", "CommonEmbedding", "MemoTable", "MemoEntry"] do
      if ← ident type label then return true
    pure false
  | [root, module, type, implementation, _] =>
    let (constructor, _) ← tag (← field implementation "Impl")
    pure (constructor = "Trait" &&
      (((← ident root "core") && (← ident module "option") && (← ident type "Option")) ||
       ((← ident root "alloc") && (← ident module "boxed") && (← ident type "Box"))))
  | [root, implementation, _] =>
    let (constructor, _) ← tag (← field implementation "Impl")
    if constructor != "Trait" then return false
    let (constructor, payload) ← tag root
    if constructor != "Builtin" then return false
    let (kind, index) ← pair payload
    let (constructor, size) ← tag kind
    pure (constructor = "Tuple" && (← size.getNat?) = 2 && (← index.getNat?) = 0)
  | _ => pure false

def optionInner (ctx : Context) (type : Json) : Read Json := do
  if (← typeKind ctx type) != .optional then throw "option type required"
  let adt ← field (← field type "Untagged") "Adt"
  match ← array (← field (← field adt "generics") "types") with
  | [inner] => pure inner
  | _ => throw "single option parameter required"

def requireKind (ctx : Context) (type : Json) (kind : Kind) : Read Unit := do
  if (← typeKind ctx type) != kind then throw "unexpected evaluator type"

def signature (ctx : Context) (function : SourceEval.Function) (decl : Json) : Read Unit := do
  let sig ← field decl "signature"
  if (← (← field sig "is_unsafe").getBool?) || (← (← field sig "is_variadic").getBool?) ||
      (← (← field sig "abi").getStr?) != "Rust" then throw "safe nonvariadic Rust ABI required"
  match function with
  | .copyWord => LookupSource.Frontend.signature ctx .copyWord decl
  | .compare => LookupSource.Frontend.signature ctx .compare decl
  | .copyResult => LookupSource.Frontend.signature ctx .copyResult decl
  | .lookup => LookupSource.Frontend.signature ctx .lookup decl
  | .concatenate => MemoSource.Frontend.signature ⟨ctx, []⟩ .concatenate decl
  | .insert => MemoSource.Frontend.signature ⟨ctx, []⟩ .insert decl
  | .chooseLonger =>
    match ← array (← field sig "inputs") with
    | [left, right] => requireKind ctx left .embedding; requireKind ctx right .embedding
    | _ => throw "two owned witnesses required"
    requireKind ctx (← field sig "output") .embedding
  | .evaluate =>
    match ← array (← field sig "inputs") with
    | [left, right, table] => sharedInput ctx left .word; sharedInput ctx right .word; requireKind ctx table .table
    | _ => throw "two shared words and owned table required"
    let output ← field sig "output"
    requireKind ctx output .tuple
    let adt ← field (← field output "Untagged") "Adt"
    match ← array (← field (← field adt "generics") "types") with
    | [result, table] => requireKind ctx (← optionInner ctx result) .embedding; requireKind ctx table .table
    | _ => throw "result/table tuple required"
  | .maximum =>
    match ← array (← field sig "inputs") with
    | [left, right] => sharedInput ctx left .word; sharedInput ctx right .word
    | _ => throw "two shared words required"
    requireKind ctx (← optionInner ctx (← field sig "output")) .embedding
  | .checkedAdd =>
    match ← array (← field sig "inputs") with
    | [left, right] => SourceEval.Frontend.unsigned32 left; SourceEval.Frontend.unsigned32 right
    | _ => throw "two u32 inputs required"
    SourceEval.Frontend.unsigned32 (← optionInner ctx (← field sig "output"))
    if (← (← field decl "body").getStr?) != "Opaque" then throw "opaque checked-add primitive required"
  | .boxNew => throw "generic Box signature checked separately"

structure ContextInfo where
  common : Context
  functions : List (Nat × SourceEval.Function)
  drops : List Nat
  roots : List (SourceEval.Function × Json)

def context (crate : Json) : Read ContextInfo := do
  let (common, _) ← LookupSource.Frontend.context crate
  let typed ← LookupSource.TypeReader.makeContext crate common
  LookupSource.TypeReader.boxMethod typed crate
  let mut functions := []
  let mut drops := []
  let mut roots := []
  for decl in ← declarations (← field crate "fun_decls") do
    let path ← array (← field (← field decl "item_meta") "name")
    let index ← (← field decl "def_id").getNat?
    if let some function ← rootName path then
      functions := functions ++ [(index, function)]
      roots := roots ++ [(function, decl)]
    else if ← boxName path then functions := functions ++ [(index, .boxNew)]
    else if ← checkedAddName path then
      signature common .checkedAdd decl
      functions := functions ++ [(index, .checkedAdd)]
    else if ← dropName path then drops := drops ++ [index]
  if !(decide (functions.map Prod.snd).Nodup) then throw "duplicate evaluator function identity"
  if !(functions.any (·.2 == .checkedAdd)) then throw "checked-add primitive missing"
  pure ⟨common, functions, drops, roots⟩

structure Definition where
  function : SourceEval.Function
  localCount : Nat
  code : Code

structure Program where
  definitions : List Definition
  covers : definitions.map Definition.function = helpers

def Program.body (program : Program) (function : SourceEval.Function) : Code :=
  ((program.definitions.find? (fun decl => decl.function == function)).map Definition.code).getD .done

def definition (ctx : ContextInfo) (fuel : Nat) (function : SourceEval.Function) : Read Definition := do
  let decl ← LookupSource.TypeReader.required (ctx.roots.lookup function)
  signature ctx.common function decl
  let body ← field (← field decl "body") "Structured"
  let locals ← field body "locals"
  if (← (← field locals "arg_count").getNat?) != arity function then throw "body input arity mismatch"
  let slots ← array (← field locals "locals")
  if slots.length ≤ arity function then throw "missing local declarations"
  let indices ← slots.mapM fun slot => do (← field slot "index").getNat?
  if indices != List.range slots.length then throw "noncanonical local indices"
  let code ← SourceEval.Frontend.sequence
    (fun index => LookupSource.TypeReader.required (ctx.functions.lookup index))
    (fun index => ctx.drops.contains index) {ctx.common with localCount := slots.length} fuel
    (← array (← field (← field body "body") "statements"))
  pure ⟨function, slots.length, code⟩

def read (json : Json) (fuel : Nat) : Read Program := do
  if (← (← field json "charon_version").getStr?) != "0.1.315" then throw "unsupported Charon version"
  if (← (← field json "has_errors").getBool?) then throw "extraction has errors"
  let crate ← field json "translated"
  if (← (← field crate "crate_name").getStr?) != "verified_ordered_core" then throw "wrong crate"
  let options ← field crate "options"
  if !(← (← field options "no_dedup_serialized_ast").getBool?) ||
      (← (← field options "preset").getStr?) != "Aeneas" then throw "unsupported extraction profile"
  let ctx ← context crate
  let defs ← helpers.mapM (definition ctx fuel)
  if hc : defs.map Definition.function = helpers then pure ⟨defs, hc⟩ else throw "helper coverage mismatch"

end SubtreeProofs.Rust.SourceEval.ProgramReader
