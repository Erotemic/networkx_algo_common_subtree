import SubtreeProofs.Rust.LookupRegionRefinement

/-! Focused type/metadata fragments, not complete compiled Rust mutations. -/

namespace LookupRegionTests

open Lean SubtreeProofs.Rust.LookupSource Heap

private def ctx : TypeReader.Context :=
  ⟨⟨[(1, .word), (2, .table), (3, .entry), (4, .embedding), (5, .optional), (6, .tuple)],
    [(10, .copyWord), (11, .compare), (12, .copyResult), (13, .lookup), (14, .boxNew)], 0⟩, 7⟩

private def rejected (value : Except String α) : Bool :=
  match value with | .error _ => true | .ok _ => false

private def reference (region : Json) : Json := json% {"Untagged":{"Ref":[$(region),
  {"Untagged":{"Adt":{"id":1,"builtin":null,
    "generics":{"regions":[],"types":[],"const_generics":[],"trait_refs":[]}}}},"Shared"]}}

-- The earlier erased reader accepts this unbound region. The scoped pass rejects it.
example : (TypeReader.type ctx none 16 (reference (json% {"Body":9}))).map
    (SourceTypes.same (.shared (.adt .word))) = .ok true := by decide +kernel
example : rejected (Regions.Reader.annotation ctx (.body 2) (reference (json% {"Body":9}))) = true := by decide +kernel
example : rejected (Regions.Reader.annotation ctx (.body 2) (reference (json% {"Var":{"Free":0}}))) = true := by decide +kernel
example : rejected (Regions.Reader.annotation ctx (.signature 1) (reference (json% {"Var":{"Free":1}}))) = true := by decide +kernel
example : rejected (Regions.Reader.annotation ctx (.body 2) (reference (json% "Erased"))) = true := by decide +kernel
example : (Regions.Reader.annotation ctx (.body 2) (reference (json% {"Body":1}))).isOk = true := by decide +kernel

-- Scope checking reaches reference annotations nested in unwind metadata too.
example : rejected (Regions.Reader.scan ctx.source (.body 2) 64
    (json% {"on_unwind":{"statements":[{"annotation":$(reference (json% {"Body":9}))}]}})) = true := by decide +kernel
example : (Regions.Reader.scan ctx.source (.body 2) 64
    (json% {"on_unwind":{"statements":[{"annotation":$(reference (json% {"Body":1}))}]}})).isOk = true := by decide +kernel

-- The helper has one region parameter; a missing instantiation is rejected.
example : rejected (Regions.Reader.roots ctx.source (json% {
    "call":{"func":{"Regular":{"kind":{"Fun":10},"generics":{"regions":[]}}}}})) = true := by decide +kernel
example : (Regions.Reader.scan ctx.source (.body 2) 64 (json% {
    "call":{"func":{"Regular":{"kind":{"Fun":10},"generics":{"regions":[{"Body":1}]}}}}})).isOk = true := by decide +kernel
example : rejected (Regions.Reader.scan ctx.source (.body 2) 64 (json% {
    "call":{"func":{"Regular":{"kind":{"Fun":10},"generics":{"regions":[{"Body":9}]}}}}})) = true := by decide +kernel

private def memory : Memory := [.node .word 0 []]
private def tagged : Regions.Ty := .shared (.body 0) (.adt .word)
private theorem safe : Borrow.Safe memory memory (.shared ⟨0, []⟩) (.shared (.adt .word)) :=
  .shared ⟨⟨_, rfl, .node .emptyWord .nil⟩⟩

example : Regions.ScopedValue memory memory (.body 1) (Regions.callLifetime memory) (.shared ⟨0, []⟩) tagged := by
  apply (Regions.scoped_erasure_iff (.refl memory) (Regions.Scoped.shared (by change 0 < 1; decide) (.adt .word)) _).mpr
  simpa only [tagged, Regions.erase] using safe

-- A valid old read alone does not make a region live in an arbitrary valuation.
example : ¬ Regions.Value memory memory (fun _ _ => False) (.shared ⟨0, []⟩) tagged := by
  intro h
  cases h with | shared _ _ hlive _ => cases hlive

-- Binder validity is independent of the common-lifetime value interpretation.
example : ¬ Regions.Scoped (.body 1) (.shared (.body 9) (.adt .word)) := by
  intro h
  cases h with
  | shared hb _ => change 9 < 1 at hb; omega

example : Regions.Scoped (.body 3)
    (Regions.rename (Regions.substitute [.body 2]) (.shared (.free 0) (.adt .word))) :=
  Regions.instantiate_scoped rfl (by intro r h; have he := List.mem_singleton.mp h; subst r; change 2 < 3; decide)
    (.shared (by change 0 < 1; decide) (.adt .word))

end LookupRegionTests
