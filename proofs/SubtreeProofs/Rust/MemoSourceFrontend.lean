module

public import SubtreeProofs.Rust.MemoSource
public import SubtreeProofs.Rust.LookupSourceFrontend

/-! Checked normal-path source syntax for the actual insertion/concatenation
helpers. Signatures distinguish the owned table input from shared inputs.
Local field/static typing, regions and heap/owner composition remain separate
from this control reader, just as in the earlier lookup control certificate. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Frontend

open Lean LookupSource
open LookupSource.Frontend hiding arity signature action sequence context function read Program

structure Context where
  common : LookupSource.Frontend.Context
  functions : List (Nat × Function)

def helpers : List Function := [.copyWord, .copyResult, .concatenate, .insert]

def rootName (path : List Json) : Read (Option Function) := do
  match path with
  | [root, last] =>
    if ← ident root "verified_ordered_core" then
      for (label, function) in [("copy_word", Function.copyWord), ("copy_result", .copyResult),
          ("concatenate", .concatenate), ("memo_insert", .insert)] do
        if ← ident last label then return some function
    pure none
  | _ => pure none

def context (crate : Json) : Read (Context × List (Function × Json)) := do
  let (common, _) ← LookupSource.Frontend.context crate
  let mut functions := []
  let mut roots := []
  for decl in ← declarations (← field crate "fun_decls") do
    let path ← array (← field (← field decl "item_meta") "name")
    let index ← (← field decl "def_id").getNat?
    if let some function ← rootName path then
      functions := functions ++ [(index, function)]
      roots := roots ++ [(function, decl)]
    else if ← boxName path then functions := functions ++ [(index, .boxNew)]
  if !(decide (functions.map Prod.snd).Nodup) then throw "duplicate supported function identity"
  pure (⟨common, functions⟩, roots)

def signature (ctx : Context) (function : Function) (decl : Json) : Read Unit := do
  let signature ← field decl "signature"
  let inputs ← array (← field signature "inputs")
  match function, inputs with
  | .copyWord, [word] => sharedInput ctx.common word .word
  | .copyResult, [result] => sharedInput ctx.common result .embedding
  | .concatenate, [left, right] => sharedInput ctx.common left .word; sharedInput ctx.common right .word
  | .insert, [table, left, right, result] =>
    if (← typeKind ctx.common table) != .table then throw "owned table input required"
    sharedInput ctx.common left .word
    sharedInput ctx.common right .word
    sharedInput ctx.common result .embedding
  | _, _ => throw "unsupported signature inputs"
  let output ← typeKind ctx.common (← field signature "output")
  let expected := match function with
    | .copyWord | .concatenate => Kind.word
    | .copyResult => .embedding
    | .insert => .table
    | .boxNew => .tuple
  if output != expected then throw "unsupported output type"

def action (ctx : Context) : LookupSource.Frontend.Context → Nat → String → Json → Read (Control.Action Function) :=
  actionWith (fun index => match ctx.functions.lookup index with
    | some function => pure function
    | none => throw "unsupported memo primitive callee") arity

def function (ctx : Context) (roots : List (Function × Json)) (fuel : Nat) (target : Function) : Read Block := do
  let decl ← match roots.lookup target with
    | some decl => pure decl
    | none => throw "required memo primitive helper missing"
  signature ctx target decl
  let body ← field (← field decl "body") "Structured"
  let locals ← field body "locals"
  if (← (← field locals "arg_count").getNat?) != arity target then throw "body argument count mismatch"
  let slots ← array (← field locals "locals")
  if slots.length ≤ arity target then throw "incomplete local declarations"
  let indices ← slots.mapM fun decl => do (← field decl "index").getNat?
  if indices != List.range slots.length then throw "noncanonical local declaration indices"
  sequenceWith (action ctx) {ctx.common with localCount := slots.length} fuel
    (← array (← field (← field body "body") "statements"))

structure Program where
  copyWord : Block
  copyResult : Block
  concatenate : Block
  insert : Block

def Program.body (program : Program) : Function → Block
  | .copyWord => program.copyWord
  | .copyResult => program.copyResult
  | .concatenate => program.concatenate
  | .insert => program.insert
  | .boxNew => .done

def read (json : Json) (fuel : Nat) : Read Program := do
  if (← (← field json "charon_version").getStr?) != "0.1.315" then throw "unsupported Charon version"
  if (← (← field json "has_errors").getBool?) then throw "Charon extraction contains errors"
  let crate ← field json "translated"
  if (← (← field crate "crate_name").getStr?) != "verified_ordered_core" then throw "wrong crate identity"
  let options ← field crate "options"
  if !(← (← field options "no_dedup_serialized_ast").getBool?) then throw "deduplicated AST unsupported"
  if (← (← field options "preset").getStr?) != "Aeneas" then throw "wrong extraction profile"
  let (ctx, roots) ← context crate
  pure ⟨← function ctx roots fuel .copyWord, ← function ctx roots fuel .copyResult,
    ← function ctx roots fuel .concatenate, ← function ctx roots fuel .insert⟩

end SubtreeProofs.Rust.MemoSource.Frontend
