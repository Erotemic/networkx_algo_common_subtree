module

public import SubtreeProofs.Rust.LookupTypedCode
public import SubtreeProofs.Rust.LookupSourceFrontend

import all Init.Control.Except

/-! Lifetime-erased type/declaration reading from retained pinned Charon data.
Regions remain in the input JSON but are not assigned a lifetime semantics.
Only the represented lookup types and generic instances are accepted. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.TypeReader

open Lean Heap Frontend SourceTypes

structure Context where
  source : Frontend.Context
  boxId : Nat

def emptyArrays (json : Json) (keys : List String) : Read Unit := do
  for key in keys do
    if !(← array (← field json key)).isEmpty then throw "unsupported generic parameters"

def genericParams (json : Json) (count : Nat) : Read Unit := do
  emptyArrays json ["regions", "const_generics", "trait_clauses", "outlives", "trait_type_constraints"]
  let types ← array (← field json "types")
  let indices ← types.mapM fun value => do (← field value "index").getNat?
  if indices != List.range count then throw "unexpected type parameter indices"

def makeContext (crate : Json) (source : Frontend.Context) : Read Context := do
  let mut boxId := none
  for decl in ← declarations (← field crate "type_decls") do
    let path ← array (← field (← field decl "item_meta") "name")
    match path with
    | [root, module, last] =>
      if (← ident root "alloc") && (← ident module "boxed") && (← ident last "Box") then
        if boxId.isSome then throw "duplicate Box declaration"
        if (← (← field decl "kind").getStr?) != "Opaque" then throw "Box must be builtin opaque"
        let (tag, payload) ← Frontend.tag (← field decl "src")
        if tag != "Builtin" || (← payload.getStr?) != "Box" then throw "wrong Box builtin identity"
        genericParams (← field decl "generics") 1
        boxId := some (← (← field decl "def_id").getNat?)
    | _ => pure ()
  match boxId with
  | none => throw "Box declaration missing"
  | some index => pure ⟨source, index⟩

def type (ctx : Context) (parameter : Option Ty := none) : Nat → Json → Read Ty
  | 0, _ => throw "type nesting budget exceeded"
  | fuel + 1, json => do
    let (constructor, payload) ← tag (← field json "Untagged")
    if constructor = "Scalar" then
      if let .str "Bool" := payload then return .boolean
      let (constructor, payload) ← tag payload
      if constructor != "Integer" then throw "unsupported scalar type"
      let (constructor, payload) ← tag payload
      if constructor != "Unsigned" || (← payload.getStr?) != "U32" then throw "u32 required"
      return .u32
    if constructor = "TypeVar" then
      let (constructor, payload) ← tag payload
      if constructor != "Free" || (← payload.getNat?) != 0 then throw "unsupported type variable"
      match parameter with
      | some ty => return ty
      | none => throw "unbound type parameter"
    if constructor = "Ref" then
      match ← array payload with
      | [_region, inner, mutability] =>
        if (← mutability.getStr?) != "Shared" then throw "mutable reference unsupported"
        return .shared (← type ctx parameter fuel inner)
      | _ => throw "invalid reference type"
    if constructor != "Adt" then throw "unsupported type constructor"
    let generics ← field payload "generics"
    emptyArrays generics ["regions", "const_generics", "trait_refs"]
    let arguments ← (← array (← field generics "types")).mapM (type ctx parameter fuel)
    let builtin ← field payload "builtin"
    let index ← (← field payload "id").getNat?
    if let .str "Box" := builtin then
      if index != ctx.boxId then throw "wrong Box type identity"
      match arguments with
      | [inner] => return .owned inner
      | _ => throw "Box requires one type argument"
    let kind ← kindRef ctx.source payload
    if let .str "Tuple" := builtin then
      if kind != .tuple then throw "wrong tuple type identity"
      return .tuple arguments
    if !builtin.isNull || kind = .tuple then throw "unsupported builtin type identity"
    if kind = .optional then
      match arguments with
      | [inner] =>
        if same inner (.adt .embedding) then return .adt .optional
        if same inner .u32 then return .option .u32
        throw "unsupported Option instance"
      | _ => throw "Option requires one type argument"
    else if !arguments.isEmpty then throw "unexpected named type arguments"
    return .adt kind
termination_by structural fuel _ => fuel

def requireType (actual expected : Ty) : Read Unit :=
  if same actual expected then pure () else throw "type mismatch"

def fields (ctx : Context) (parameter : Option Ty) (json : Json)
    (labels : List String) (positional : Bool) : Read (List Ty) := do
  let values ← array json
  if values.length != labels.length then throw "field count mismatch"
  for (value, label) in values.zip labels do
    if (← (← field value "name").getStr?) != label then throw "field name/order mismatch"
    if (← (← field value "is_positional").getBool?) != positional then throw "field position kind mismatch"
  values.mapM fun value => do type ctx parameter 64 (← field value "ty")

structure Layout where
  kind : Kind
  variant : Nat
  fields : List Ty

def layoutCheck (layout : Layout) : Bool :=
  match constructorFields layout.kind layout.variant (.adt layout.kind) with
  | none => false
  | some expected => sameList layout.fields expected

theorem layoutCheck_sound {layout : Layout} (h : layoutCheck layout = true) :
    Shape layout.kind layout.variant layout.fields (.adt layout.kind) := by
  unfold layoutCheck at h
  cases hs : constructorFields layout.kind layout.variant (.adt layout.kind) with
  | none => simp [hs] at h
  | some expected =>
    have he := sameList_eq (by simpa only [hs] using h)
    rw [← he] at hs
    exact constructorFields_sound hs

def enumLayout (ctx : Context) (kind : Kind) (json : Json) (labels : List String)
    (fieldLabels : List (List String)) (parameter : Option Ty) : Read (List Layout) := do
  let variants ← array json
  if variants.length != labels.length || variants.length != fieldLabels.length then throw "variant count mismatch"
  let mut result := []
  for ((variant, label), (index, names)) in (variants.zip labels).zip ((List.range variants.length).zip fieldLabels) do
    if (← (← field variant "id").getNat?) != index then throw "variant ID/order mismatch"
    if (← (← field variant "name").getStr?) != label then throw "variant name/order mismatch"
    let (tag, value) ← Frontend.tag (← field variant "discriminant")
    let (sign, number) ← pair value
    let encoded ← match index with
      | 0 => pure "0"
      | 1 => pure "1"
      | _ => throw "only binary enum variants are represented"
    if tag != "Signed" || (← sign.getStr?) != "Isize" || (← number.getStr?) != encoded then
      throw "unsupported discriminant encoding"
    result := result ++ [⟨kind, index, ← fields ctx parameter (← field variant "fields") names true⟩]
  pure result

def readLayouts (ctx : Context) (crate : Json) : Read (List Layout) := do
  let mut result := []
  for decl in ← declarations (← field crate "type_decls") do
    let path ← array (← field (← field decl "item_meta") "name")
    if let some kind ← kindName path then
      genericParams (← field decl "generics") (if kind = .optional then 1 else 0)
      if kind = .tuple then
        if (← (← field decl "kind").getStr?) != "Opaque" then throw "tuple must be builtin opaque"
        let (tag, payload) ← Frontend.tag (← field decl "src")
        if tag != "Builtin" || (← payload.getStr?) != "Tuple" then throw "wrong tuple builtin"
      else
        let (constructor, payload) ← tag (← field decl "kind")
        if kind = .word || kind = .table || kind = .optional then
          if constructor != "Enum" then throw "enum declaration required"
          let labels := if kind = .word then ["Empty", "Pair"] else
            if kind = .table then ["Empty", "Entry"] else ["None", "Some"]
          let names := if kind = .optional then [[], ["_0"]] else [[], ["_0", "_1"]]
          result := result ++ (← enumLayout ctx kind payload labels names
            (if kind = .optional then some (.adt .embedding) else none))
        else
          if constructor != "Struct" then throw "struct declaration required"
          let labels := if kind = .entry then ["left", "right", "result"] else ["word", "edges"]
          result := result ++ [⟨kind, 0, ← fields ctx none payload labels false⟩]
  for kind in [Kind.word, .table, .entry, .embedding, .optional] do
    if !(result.any fun layout => layout.kind == kind) then throw "required type declaration missing"
  pure result

def layouts (ctx : Context) (crate : Json) : Read (List Layout) := do
  let result ← readLayouts ctx crate
  if result.all layoutCheck then pure result else throw "declaration fields disagree with heap Shape"

theorem layouts_sound {ctx : Context} {crate : Json} {result : List Layout}
    (h : layouts ctx crate = .ok result) :
    ∀ layout ∈ result, Shape layout.kind layout.variant layout.fields (.adt layout.kind) := by
  unfold layouts at h
  cases hr : readLayouts ctx crate with
  | error message => simp only [hr, bind, Except.bind] at h; cases h
  | ok result' =>
    simp only [hr, bind, Except.bind] at h
    split at h
    next hc =>
      cases h
      intro layout hl
      exact layoutCheck_sound (List.all_eq_true.mp hc layout hl)
    next => cases h

end SubtreeProofs.Rust.LookupSource.TypeReader
