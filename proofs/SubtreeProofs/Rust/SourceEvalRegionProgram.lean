module

public import SubtreeProofs.Rust.SourceEvalTypeReader
public import SubtreeProofs.Rust.LookupRegionScope

/-! Actual expanded-profile region annotations and binder-use coverage, reusing
shared type attachment and complete JSON descendant scanning. This retains the
scoped declarations; caller-local borrow lifetimes are a separate interpretation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Regions

open Lean LookupSource LookupSource.Heap
open LookupSource.Heap.Regions LookupSource.Heap.Regions.Reader
open LookupSource.Frontend (Read field array)

def regionArity : SourceEval.Function → Nat
  | .copyWord | .copyResult => 1
  | .compare | .concatenate | .evaluate | .maximum => 2
  | .lookup | .insert => 3
  | .chooseLonger | .boxNew | .checkedAdd => 0

def calleeRegions (info : ProgramReader.ContextInfo) : CalleeRegions := fun index => do
  let function ← LookupSource.TypeReader.required (info.functions.lookup index)
  pure (regionArity function)

structure Definition (ctx : LookupSource.TypeReader.Context) (arity : CalleeRegions) where
  source : SourceEval.TypeReader.Definition
  freeCount : Nat
  bodyCount : Nat
  signatureJson : Json
  bodyJson : Json
  parameters : CheckedFields (.signature freeCount) (Types.inputs source.source.function)
  result : Checked (.signature freeCount) (Types.output source.source.function)
  locals : CheckedFields (.body bodyCount) source.locals
  signatureScope : TreeWith arity (.signature freeCount) signatureJson
  bodyScope : TreeWith arity (.body bodyCount) bodyJson

def Definition.function {ctx : LookupSource.TypeReader.Context} {arity : CalleeRegions}
    (definition : Definition ctx arity) : SourceEval.Function := definition.source.source.function

def definition (ctx : LookupSource.TypeReader.Context) (info : ProgramReader.ContextInfo)
    (decl : SourceEval.TypeReader.Definition) : Read (Definition ctx (calleeRegions info)) := do
  let raw ← LookupSource.TypeReader.required (info.roots.lookup decl.source.function)
  let generics ← field raw "generics"
  let parameters ← array (← field generics "regions")
  let indices ← parameters.mapM fun parameter => do (← field parameter "index").getNat?
  if indices != List.range parameters.length then throw "noncanonical signature region binders"
  if parameters.length != regionArity decl.source.function then throw "signature region arity mismatch"
  for parameter in parameters do
    if !(← (← field parameter "late_bound").getBool?) then throw "early-bound signature lifetime unsupported"
  LookupSource.TypeReader.emptyArrays generics ["outlives", "trait_type_constraints"]
  let signature ← field raw "signature"
  let args ← annotations ctx (.signature parameters.length) (← array (← field signature "inputs"))
  let result ← annotation ctx (.signature parameters.length) (← field signature "output")
  let body ← field (← field raw "body") "Structured"
  let count ← (← field body "bound_body_regions").getNat?
  let slots ← array (← field (← field body "locals") "locals")
  let locals ← annotations ctx (.body count) (← slots.mapM fun slot => field slot "ty")
  let sigScope ← scanWith (calleeRegions info) (.signature parameters.length) 512 signature
  let bodyScope ← scanWith (calleeRegions info) (.body count) 512 body
  if hi : SourceTypes.sameList args.erased (Types.inputs decl.source.function) = true then
    if ho : SourceTypes.same result.erased (Types.output decl.source.function) = true then
      if hl : SourceTypes.sameList locals.erased decl.locals = true then
        pure ⟨decl, parameters.length, count, signature, body,
          by simpa only [SourceTypes.sameList_eq hi] using args.checked,
          by simpa only [SourceTypes.same_eq ho] using result.checked,
          by simpa only [SourceTypes.sameList_eq hl] using locals.checked,
          sigScope.proof, bodyScope.proof⟩
      else throw "regional/local type mismatch"
    else throw "regional/output type mismatch"
  else throw "regional/parameter type mismatch"

structure Program where
  typed : SourceEval.TypeReader.Program
  context : LookupSource.TypeReader.Context
  info : ProgramReader.ContextInfo
  definitions : List (Definition context (calleeRegions info))
  aligned : definitions.map (fun decl => decl.source.source) = typed.source.definitions

def read (json : Json) : Read Program := do
  let typed ← SourceEval.TypeReader.read json 512
  let crate ← field json "translated"
  let info ← ProgramReader.context crate
  let ctx ← LookupSource.TypeReader.makeContext crate info.common
  let defs ← typed.definitions.mapM (definition ctx info)
  if hd : defs.map (fun decl => decl.source.source) = typed.source.definitions then
    pure ⟨typed, ctx, info, defs, hd⟩
  else throw "regional/source definition alignment failed"

def check (json : Json) (body : SourceEval.Function → SourceEval.Code) : Bool :=
  match read json with
  | .error _ => false
  | .ok program => program.definitions.all fun decl =>
      decide (decl.source.source.code = body decl.function) && decide (decl.freeCount = regionArity decl.function)

theorem check_sound {json : Json} {body : SourceEval.Function → SourceEval.Code} (h : check json body = true) :
    ∃ program, read json = .ok program ∧
      ∀ function ∈ ProgramReader.helpers, ∃ decl ∈ program.definitions,
        decl.function = function ∧ decl.source.source.code = body function ∧ decl.freeCount = regionArity function := by
  cases hr : read json with
  | error message => simp [check, hr] at h
  | ok program =>
    refine ⟨program, rfl, ?_⟩
    intro function hf
    have hm : function ∈ program.definitions.map Definition.function := by
      have hm : function ∈ (program.definitions.map (fun decl => decl.source.source)).map ProgramReader.Definition.function := by
        rw [program.aligned, program.typed.source.covers]
        exact hf
      change function ∈ program.definitions.map (fun decl => decl.source.source.function)
      simpa only [List.map_map, Function.comp_def] using hm
    obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
    have hc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (by simpa only [check, hr] using h) decl hd)
    exact ⟨decl, hd, he, by simpa only [he] using of_decide_eq_true hc.1,
      by simpa only [he] using of_decide_eq_true hc.2⟩

end SubtreeProofs.Rust.SourceEval.Regions
