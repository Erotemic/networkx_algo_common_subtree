module

public import SubtreeProofs.Rust.SourceEvalTypeAnnotations

/-! Whole-profile lifetime-erased declarations and static constraints, tied to
exactly the code returned by the existing source reader. Every normal arm is
checked. Region interpretation and operational safety are separate layers. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.TypeReader

open Lean LookupSource Heap
open LookupSource.Frontend hiding Context Program read arity signature
open LookupSource.TypeReader hiding Definition Program definition read check

structure Definition where
  source : ProgramReader.Definition
  locals : List Ty
  count : locals.length = source.localCount
  boundary : locals.take ((Types.inputs source.function).length + 1) =
    Types.output source.function :: Types.inputs source.function
  constraints : Types.CodeConstraints locals (Types.output source.function) source.code

def definition (info : ProgramReader.ContextInfo) (ctx : Context) (fuel : Nat)
    (source : ProgramReader.Definition) : Read Definition := do
  let decl ← required (info.roots.lookup source.function)
  let generics ← field decl "generics"
  emptyArrays generics ["types", "const_generics", "trait_clauses", "outlives", "trait_type_constraints"]
  let signature ← field decl "signature"
  let parameters ← (← array (← field signature "inputs")).mapM (type ctx none 64)
  if !SourceTypes.sameList parameters (Types.inputs source.function) then throw "parameter type mismatch"
  requireType (← type ctx none 64 (← field signature "output")) (Types.output source.function)
  let body ← field (← field decl "body") "Structured"
  let slots ← array (← field (← field body "locals") "locals")
  let locals ← slots.mapM fun slot => do type ctx none 64 (← field slot "ty")
  if hn : locals.length = source.localCount then
    if hb : SourceTypes.sameList (locals.take ((Types.inputs source.function).length + 1))
        (Types.output source.function :: Types.inputs source.function) = true then
      statementAnnotations info ctx locals fuel (← array (← field (← field body "body") "statements"))
      if hc : Types.checkCode locals (Types.output source.function) source.code = true then
        pure ⟨source, locals, hn, SourceTypes.sameList_eq hb, Types.checkCode_sound hc⟩
      else throw "code type constraints failed"
    else throw "return/argument local type mismatch"
  else throw "local declaration count mismatch"

/-- Check the generic Option declaration at its second actual instance too.
Checking only its embedding instance would accept a field hard-coded to an
embedding instead of the source type parameter. -/
def scoreLayouts (ctx : Context) (crate : Json) : Read (List LookupSource.TypeReader.Layout) := do
  for decl in ← declarations (← field crate "type_decls") do
    let path ← array (← field (← field decl "item_meta") "name")
    if (← kindName path) = some .optional then
      let payload ← field (← field decl "kind") "Enum"
      return ← enumLayout ctx .optional payload ["None", "Some"] [[], ["_0"]] (some .u32)
  throw "generic Option declaration missing"

def scoreLayoutCheck (layout : LookupSource.TypeReader.Layout) : Bool :=
  match SourceTypes.constructorFields layout.kind layout.variant (.option .u32) with
  | none => false
  | some expected => SourceTypes.sameList layout.fields expected

theorem scoreLayoutCheck_sound {layout : LookupSource.TypeReader.Layout} (h : scoreLayoutCheck layout = true) :
    Shape layout.kind layout.variant layout.fields (.option .u32) := by
  unfold scoreLayoutCheck at h
  cases hs : SourceTypes.constructorFields layout.kind layout.variant (.option .u32) with
  | none => simp [hs] at h
  | some expected =>
    have he := SourceTypes.sameList_eq (by simpa only [hs] using h)
    rw [← he] at hs
    exact SourceTypes.constructorFields_sound hs

structure Program where
  source : ProgramReader.Program
  layouts : List LookupSource.TypeReader.Layout
  layouts_sound : ∀ layout ∈ layouts, Shape layout.kind layout.variant layout.fields (.adt layout.kind)
  scoreLayouts : List LookupSource.TypeReader.Layout
  scoreLayouts_sound : ∀ layout ∈ scoreLayouts, Shape layout.kind layout.variant layout.fields (.option .u32)
  definitions : List Definition
  aligned : definitions.map Definition.source = source.definitions

def read (json : Json) (fuel : Nat) : Read Program := do
  let source ← ProgramReader.read json fuel
  let crate ← field json "translated"
  let info ← ProgramReader.context crate
  let ctx ← makeContext crate info.common
  let shapes ← layouts ctx crate
  let scores ← scoreLayouts ctx crate
  let defs ← source.definitions.mapM (definition info ctx fuel)
  if hs : shapes.all layoutCheck = true then
    if hu : scores.all scoreLayoutCheck = true then
      if hd : defs.map Definition.source = source.definitions then
        pure ⟨source, shapes, fun layout hl => layoutCheck_sound (List.all_eq_true.mp hs layout hl),
          scores, fun layout hl => scoreLayoutCheck_sound (List.all_eq_true.mp hu layout hl), defs, hd⟩
      else throw "typed/source definition alignment failed"
    else throw "score Option layout constraints failed"
  else throw "layout constraints failed"

def check (json : Json) (fuel : Nat) (body : SourceEval.Function → SourceEval.Code) : Bool :=
  match read json fuel with
  | .error _ => false
  | .ok program => program.definitions.all fun decl => decide (decl.source.code = body decl.source.function)

theorem check_sound {json : Json} {fuel : Nat} {body : SourceEval.Function → SourceEval.Code}
    (h : check json fuel body = true) :
    ∃ program, read json fuel = .ok program ∧
      (∀ layout ∈ program.layouts, Shape layout.kind layout.variant layout.fields (.adt layout.kind)) ∧
      (∀ layout ∈ program.scoreLayouts, Shape layout.kind layout.variant layout.fields (.option .u32)) ∧
      ∀ decl ∈ program.definitions,
        Types.CodeConstraints decl.locals (Types.output decl.source.function) (body decl.source.function) := by
  cases hr : read json fuel with
  | error message => simp [check, hr] at h
  | ok program =>
    refine ⟨program, rfl, program.layouts_sound, program.scoreLayouts_sound, ?_⟩
    intro decl hd
    have he : decl.source.code = body decl.source.function := of_decide_eq_true
      (List.all_eq_true.mp (by simpa only [check, hr] using h) decl hd)
    simpa only [← he] using decl.constraints

theorem check_boundaries {json : Json} {fuel : Nat} {body : SourceEval.Function → SourceEval.Code}
    (h : check json fuel body = true) (function : SourceEval.Function)
    (hf : function ∈ ProgramReader.helpers) :
    ∃ locals, locals.take ((Types.inputs function).length + 1) = Types.output function :: Types.inputs function ∧
      Types.CodeConstraints locals (Types.output function) (body function) := by
  obtain ⟨program, _, _, _, ht⟩ := check_sound h
  have hm : function ∈ program.definitions.map (fun decl => decl.source.function) := by
    have hm : function ∈ (program.definitions.map Definition.source).map ProgramReader.Definition.function := by
      rw [program.aligned, program.source.covers]
      exact hf
    simpa only [List.map_map, Function.comp_def] using hm
  obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
  have hc := ht decl hd
  have hb := decl.boundary
  rw [he] at hc hb
  exact ⟨decl.locals, hb, hc⟩

end SubtreeProofs.Rust.SourceEval.TypeReader
