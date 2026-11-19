module

public import SubtreeProofs.Rust.MemoTypeCertificate
public import SubtreeProofs.Rust.LookupRegionScope
public import SubtreeProofs.Rust.LookupBorrowLoans

/-! Actual memo source region binding and annotation erasure. Insertion has
four value arguments but only three signature lifetimes: its table is owned.
This is scope checking, separate from dynamic loan/lifetime interpretation. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Regions

open Lean LookupSource LookupSource.Heap
open LookupSource.Heap.Regions LookupSource.Heap.Regions.Reader
open LookupSource.Frontend (Read field array)

def regionArity : Function → Nat
  | .copyWord | .copyResult => 1
  | .concatenate => 2
  | .insert => 3
  | .boxNew => 0

def calleeRegions (memo : Frontend.Context) : CalleeRegions := fun index => do
  let function ← LookupSource.TypeReader.required (memo.functions.lookup index)
  pure (regionArity function)

structure Definition (ctx : LookupSource.TypeReader.Context) (arity : CalleeRegions) where
  source : TypeReader.Definition
  freeCount : Nat
  bodyCount : Nat
  signatureJson : Json
  bodyJson : Json
  parameters : CheckedFields (.signature freeCount) (Types.inputs source.function)
  result : Checked (.signature freeCount) (Types.output source.function)
  locals : CheckedFields (.body bodyCount) source.locals
  signatureScope : TreeWith arity (.signature freeCount) signatureJson
  bodyScope : TreeWith arity (.body bodyCount) bodyJson

def Definition.function {ctx : LookupSource.TypeReader.Context} {arity : CalleeRegions}
    (definition : Definition ctx arity) : Function := definition.source.function

def definition (ctx : LookupSource.TypeReader.Context) (memo : Frontend.Context)
    (roots : List (Function × Json)) (decl : TypeReader.Definition) : Read (Definition ctx (calleeRegions memo)) := do
  let raw ← LookupSource.TypeReader.required (roots.lookup decl.function)
  let generics ← field raw "generics"
  let parameters ← array (← field generics "regions")
  let indices ← parameters.mapM fun parameter => do (← field parameter "index").getNat?
  if indices != List.range parameters.length then throw "noncanonical memo signature region binders"
  if parameters.length != regionArity decl.function then throw "unsupported memo signature region arity"
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
  let sigScope ← scanWith (calleeRegions memo) (.signature parameters.length) 512 signature
  let bodyScope ← scanWith (calleeRegions memo) (.body count) 512 body
  if hi : SourceTypes.sameList args.erased (Types.inputs decl.function) = true then
    if ho : SourceTypes.same result.erased (Types.output decl.function) = true then
      if hl : SourceTypes.sameList locals.erased decl.locals = true then
        pure ⟨decl, parameters.length, count, signature, body,
          by simpa only [SourceTypes.sameList_eq hi] using args.checked,
          by simpa only [SourceTypes.same_eq ho] using result.checked,
          by simpa only [SourceTypes.sameList_eq hl] using locals.checked,
          sigScope.proof, bodyScope.proof⟩
      else throw "memo region/local type mismatch"
    else throw "memo region/output type mismatch"
  else throw "memo region/parameter type mismatch"

structure Program where
  typed : TypeReader.Program
  context : LookupSource.TypeReader.Context
  memo : Frontend.Context
  definitions : List (Definition context (calleeRegions memo))
  covers : definitions.map Definition.function = [.copyWord, .copyResult, .concatenate, .insert]

def read (json : Json) : Read Program := do
  let typed ← TypeReader.read json 512
  let crate ← field json "translated"
  let (memo, roots) ← Frontend.context crate
  let ctx ← LookupSource.TypeReader.makeContext crate memo.common
  let defs ← typed.definitions.mapM (definition ctx memo roots)
  if hc : defs.map Definition.function = [.copyWord, .copyResult, .concatenate, .insert] then
    pure ⟨typed, ctx, memo, defs, hc⟩
  else throw "memo region definition coverage mismatch"

def check (json : Json) (body : Function → MemoSource.Code) : Bool :=
  match read json with
  | .error _ => false
  | .ok program => program.definitions.all fun decl =>
      decide (decl.source.code = body decl.function) &&
        LookupSource.Heap.Borrow.codeRoutes decl.source.locals decl.source.code

theorem check_sound {json : Json} {body : Function → MemoSource.Code} (h : check json body = true) :
    ∃ program, read json = .ok program ∧
      ∀ function, function ≠ .boxNew → ∃ decl ∈ program.definitions,
        decl.function = function ∧ decl.source.code = body function ∧
          LookupSource.Heap.Borrow.codeRoutes decl.source.locals (body function) = true := by
  cases hr : read json with
  | error message => simp [check, hr] at h
  | ok program =>
    refine ⟨program, rfl, ?_⟩
    intro function hf
    have hm : function ∈ program.definitions.map Definition.function := by
      rw [program.covers]
      cases function <;> simp_all
    obtain ⟨decl, hd, he⟩ := List.mem_map.mp hm
    have hc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (by simpa only [check, hr] using h) decl hd)
    have hcode : decl.source.code = body function := by simpa only [he] using of_decide_eq_true hc.1
    exact ⟨decl, hd, he, hcode, by simpa only [hcode] using hc.2⟩

end SubtreeProofs.Rust.MemoSource.Regions
