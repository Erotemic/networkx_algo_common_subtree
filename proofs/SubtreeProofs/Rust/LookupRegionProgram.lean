module

public import SubtreeProofs.Rust.LookupRegionScope

/-! Scoped region annotations for every selected source helper, together with
complete signature/body region-use coverage and existing static constraints.
Function region arguments have the checked pinned signature arities. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader

open Lean Frontend

structure Definition (ctx : TypeReader.Context) where
  source : TypeReader.Definition
  freeCount : Nat
  bodyCount : Nat
  signatureJson : Json
  bodyJson : Json
  parameters : CheckedFields (.signature freeCount) (SourceTypes.inputs source.function)
  result : Checked (.signature freeCount) (SourceTypes.output source.function)
  locals : CheckedFields (.body bodyCount) source.locals
  signatureScope : Tree ctx.source (.signature freeCount) signatureJson
  bodyScope : Tree ctx.source (.body bodyCount) bodyJson

def Definition.function {ctx : TypeReader.Context} (definition : Definition ctx) : Function := definition.source.function

def definition (ctx : TypeReader.Context) (roots : List (Function × Json)) (decl : TypeReader.Definition) :
    Read (Definition ctx) := do
  let raw ← TypeReader.required (roots.lookup decl.function)
  let generics ← field raw "generics"
  let parameters ← array (← field generics "regions")
  let indices ← parameters.mapM fun parameter => do (← field parameter "index").getNat?
  if indices != List.range parameters.length then throw "noncanonical signature region binders"
  if parameters.length != Frontend.arity decl.function then throw "unsupported signature region arity"
  for parameter in parameters do
    if !(← (← field parameter "late_bound").getBool?) then throw "early-bound signature lifetime unsupported"
  TypeReader.emptyArrays generics ["outlives", "trait_type_constraints"]
  let signature ← field raw "signature"
  let args ← annotations ctx (.signature parameters.length) (← array (← field signature "inputs"))
  let result ← annotation ctx (.signature parameters.length) (← field signature "output")
  let body ← field (← field raw "body") "Structured"
  let count ← (← field body "bound_body_regions").getNat?
  let slots ← array (← field (← field body "locals") "locals")
  let locals ← annotations ctx (.body count) (← slots.mapM fun slot => field slot "ty")
  let sigScope ← scan ctx.source (.signature parameters.length) 512 signature
  let bodyScope ← scan ctx.source (.body count) 512 body
  if hi : SourceTypes.sameList args.erased (SourceTypes.inputs decl.function) = true then
    if ho : SourceTypes.same result.erased (SourceTypes.output decl.function) = true then
      if hl : SourceTypes.sameList locals.erased decl.locals = true then
        pure ⟨decl, parameters.length, count, signature, body,
          by simpa only [SourceTypes.sameList_eq hi] using args.checked,
          by simpa only [SourceTypes.same_eq ho] using result.checked,
          by simpa only [SourceTypes.sameList_eq hl] using locals.checked,
          sigScope.proof, bodyScope.proof⟩
      else throw "scoped local annotations disagree with existing declarations"
    else throw "scoped output disagrees with existing signature"
  else throw "scoped parameters disagree with existing signature"

structure Program where
  context : TypeReader.Context
  definitions : List (Definition context)
  covers : definitions.map Definition.function = [.copyWord, .compare, .copyResult, .lookup]

def read (json : Json) : Read Program := do
  let typed ← TypeReader.read json 512
  let crate ← field json "translated"
  let (source, roots) ← Frontend.context crate
  let ctx ← TypeReader.makeContext crate source
  let defs ← typed.definitions.mapM (definition ctx roots)
  if hc : defs.map Definition.function = [.copyWord, .compare, .copyResult, .lookup] then
    pure ⟨ctx, defs, hc⟩
  else throw "scoped definition coverage mismatch"

def check (json : Json) (body : Function → LookupSource.Code) : Bool :=
  match read json with
  | .error _ => false
  | .ok program => program.definitions.all fun decl =>
      decide (decl.source.code = body decl.function) && Borrow.codeRoutes decl.source.locals decl.source.code

theorem check_sound {json : Json} {body : Function → LookupSource.Code} (h : check json body = true) :
    ∃ program, read json = .ok program ∧
      ∀ function, function ≠ .boxNew → ∃ decl ∈ program.definitions,
        decl.function = function ∧ decl.source.code = body function ∧ Borrow.codeRoutes decl.source.locals (body function) = true := by
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

end SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader
