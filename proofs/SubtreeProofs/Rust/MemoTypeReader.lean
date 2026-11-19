module

public import SubtreeProofs.Rust.MemoSourceTypes
public import SubtreeProofs.Rust.LookupTypeAnnotations

/-! Intrinsically certified source layouts, signatures, local prefixes and
static constraints for the actual memo helper set. Nested source annotations
reuse the checked common reader and a supplied memo callee interpretation. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.TypeReader

open Lean LookupSource LookupSource.Heap LookupSource.SourceTypes
open LookupSource.TypeReader hiding Definition Program definition read check check_sound check_functions check_boundaries
open LookupSource.Frontend hiding Context Program context signature function read action sequence check

structure Definition where
  function : Function
  locals : List Ty
  code : MemoSource.Code
  boundary : locals.take ((Types.inputs function).length + 1) = Types.output function :: Types.inputs function
  constraints : Types.CodeConstraints locals (Types.output function) code

def definition (ctx : LookupSource.TypeReader.Context) (memo : MemoSource.Frontend.Context)
    (roots : List (Function × Json)) (fuel : Nat) (function : Function) : Read Definition := do
  let decl ← required (roots.lookup function)
  let generics ← field decl "generics"
  emptyArrays generics ["types", "const_generics", "trait_clauses", "outlives", "trait_type_constraints"]
  let signature ← field decl "signature"
  if (← (← field signature "is_unsafe").getBool?) || (← (← field signature "is_variadic").getBool?) then
    throw "unsafe/variadic helper signature"
  if (← (← field signature "abi").getStr?) != "Rust" then throw "Rust ABI required"
  let parameters ← (← array (← field signature "inputs")).mapM (type ctx none 64)
  if !sameList parameters (Types.inputs function) then throw "memo helper parameter types mismatch"
  requireType (← type ctx none 64 (← field signature "output")) (Types.output function)
  let body ← field (← field decl "body") "Structured"
  let slots ← array (← field (← field body "locals") "locals")
  let locals ← slots.mapM fun slot => do type ctx none 64 (← field slot "ty")
  if hb : sameList (locals.take ((Types.inputs function).length + 1)) (Types.output function :: Types.inputs function) = true then
    let source ← MemoSource.Frontend.function memo roots fuel function
    let code ← required (Control.lower source)
    statementAnnotationsWith (MemoSource.Frontend.action memo) Types.callOutput (fun f => decide (f = .boxNew))
      ctx locals fuel (← array (← field (← field body "body") "statements"))
    if hc : Types.checkCode locals (Types.output function) code = true then
      pure ⟨function, locals, code, sameList_eq hb, checkCodeWith_sound hc⟩
    else throw "normalized memo code type constraints failed"
  else throw "memo return/argument local type mismatch"

structure Program where
  layouts : List Layout
  layouts_sound : ∀ layout ∈ layouts, Shape layout.kind layout.variant layout.fields (.adt layout.kind)
  definitions : List Definition
  covers : definitions.map Definition.function = [.copyWord, .copyResult, .concatenate, .insert]

def read (json : Json) (fuel : Nat) : Read Program := do
  let _ ← MemoSource.Frontend.read json fuel
  let crate ← field json "translated"
  let (memo, roots) ← MemoSource.Frontend.context crate
  let ctx ← makeContext crate memo.common
  boxMethod ctx crate
  let shapes ← layouts ctx crate
  let defs ← [Function.copyWord, .copyResult, .concatenate, .insert].mapM (definition ctx memo roots fuel)
  if hs : shapes.all layoutCheck = true then
    if hd : defs.map Definition.function = [.copyWord, .copyResult, .concatenate, .insert] then
      pure ⟨shapes, fun layout hl => layoutCheck_sound (List.all_eq_true.mp hs layout hl), defs, hd⟩
    else throw "memo helper coverage mismatch"
  else throw "memo layout proof check failed"

def check (json : Json) (fuel : Nat) (body : Function → MemoSource.Code) : Bool :=
  match read json fuel with
  | .error _ => false
  | .ok program => program.definitions.all fun decl => decide (decl.code = body decl.function)

theorem check_sound {json : Json} {fuel : Nat} {body : Function → MemoSource.Code}
    (h : check json fuel body = true) :
    ∃ program, read json fuel = .ok program ∧
      (∀ layout ∈ program.layouts, Shape layout.kind layout.variant layout.fields (.adt layout.kind)) ∧
      ∀ decl ∈ program.definitions, Types.CodeConstraints decl.locals (Types.output decl.function) (body decl.function) := by
  cases hr : read json fuel with
  | error message => simp [check, hr] at h
  | ok program =>
    refine ⟨program, rfl, program.layouts_sound, ?_⟩
    intro decl hd
    have he : decl.code = body decl.function := of_decide_eq_true
      (List.all_eq_true.mp (by simpa only [check, hr] using h) decl hd)
    simpa only [← he] using decl.constraints

theorem check_boundaries {json : Json} {fuel : Nat} {body : Function → MemoSource.Code}
    (h : check json fuel body = true) (function : Function) (hf : function ≠ .boxNew) :
    ∃ locals, locals.take ((Types.inputs function).length + 1) = Types.output function :: Types.inputs function ∧
      Types.CodeConstraints locals (Types.output function) (body function) := by
  obtain ⟨program, _, _, ht⟩ := check_sound h
  have hm : function ∈ program.definitions.map Definition.function := by
    rw [program.covers]
    cases function <;> simp_all
  obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
  have hc := ht decl hd
  have hb := decl.boundary
  rw [he] at hc hb
  exact ⟨decl.locals, hb, hc⟩

end SubtreeProofs.Rust.MemoSource.TypeReader
