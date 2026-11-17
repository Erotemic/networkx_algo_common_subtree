import SubtreeProofs.Rust.MemoTypeRefinement

/-! Focused source/type/region fragments, not compiled Rust mutations. Complete
actual extraction is checked separately by the imported kernel certificates. -/

namespace MemoTypeTests

open Lean SubtreeProofs.Rust LookupSource LookupSource.Heap

private def locals : List Ty := [.adt .table, .adt .table, .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)]
private def forward : MemoSource.Code :=
  .step (.call .insert [.move 1, .move 2, .move 3, .move 4] 0) .ret

-- The table is moved as a value, while the other three inputs are shared.
example : MemoSource.Types.checkCode locals (.adt .table) forward = true := by decide +kernel
example : SourceTypes.inferOperand locals (.copy (.local 1)) = none := rfl
example : SourceTypes.sameList (MemoSource.Types.inputs .insert)
    [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word), .shared (.adt .embedding)] = false := by decide +kernel
example : MemoSource.Types.checkCode [.adt .table, .owned (.adt .table), .shared (.adt .word),
    .shared (.adt .word), .shared (.adt .embedding)] (.adt .table) forward = false := by decide +kernel

-- Static local declarations do not supply initialized arguments.
example : Heap.exec (MemoSource.Heap.run MemoSource.Program.body 4) forward [] (initialLocals []) = none := rfl

private def memo : MemoSource.Frontend.Context :=
  ⟨⟨[(1, .word), (2, .table), (3, .entry), (4, .embedding), (5, .tuple), (6, .optional)], [], 16⟩,
    [(10, .copyWord), (11, .copyResult), (12, .concatenate), (13, .insert), (14, .boxNew)]⟩
private def ctx : TypeReader.Context := ⟨memo.common, 7⟩
private def rejected (value : Except String α) : Bool := match value with | .error _ => true | .ok _ => false
private def falsePlace : Json := json% {"kind":{"Local":1},"ty":{"Untagged":{"Scalar":"Bool"}}}

-- Control syntax ignores the false annotation; the typed pass rejects it.
example : Frontend.place memo.common 8 falsePlace = .ok (.local 1) := by decide +kernel
example : rejected (TypeReader.placeAnnotations ctx locals 8 falsePlace) = true := by decide +kernel

-- Value arity is four; region arity is three because the table is owned.
example : MemoSource.arity .insert = 4 := rfl
example : MemoSource.Regions.regionArity .insert = 3 := rfl
example : (Heap.Regions.Reader.rootsWith (MemoSource.Regions.calleeRegions memo) (json% {
    "call":{"func":{"Regular":{"kind":{"Fun":13},"generics":{"regions":[{"Body":0},{"Body":1},{"Body":2}]}}}}})).isOk = true := by decide +kernel
example : rejected (Heap.Regions.Reader.rootsWith (MemoSource.Regions.calleeRegions memo) (json% {
    "call":{"func":{"Regular":{"kind":{"Fun":13},"generics":{"regions":[{"Body":0},{"Body":1},{"Body":2},{"Body":3}]}}}}})) = true := by decide +kernel
example : rejected (Heap.Regions.Reader.scanWith (MemoSource.Regions.calleeRegions memo) (.body 2) 64 (json% {
    "call":{"func":{"Regular":{"kind":{"Fun":13},"generics":{"regions":[{"Body":0},{"Body":1},{"Body":2}]}}}}})) = true := by decide +kernel

private def reference (region : Json) : Json := json% {"Untagged":{"Ref":[$(region),
  {"Untagged":{"Adt":{"id":1,"builtin":null,
    "generics":{"regions":[],"types":[],"const_generics":[],"trait_refs":[]}}}},"Shared"]}}

example : (Heap.Regions.Reader.annotation ctx (.signature 3) (reference (json% {"Var":{"Free":2}}))).isOk = true := by decide +kernel
example : rejected (Heap.Regions.Reader.annotation ctx (.signature 3) (reference (json% {"Var":{"Free":3}}))) = true := by decide +kernel
-- Gapped body IDs are valid within the declared binder count.
example : (Heap.Regions.Reader.annotation ctx (.body 33) (reference (json% {"Body":31}))).isOk = true := by decide +kernel
example : rejected (Heap.Regions.Reader.annotation ctx (.body 33) (reference (json% {"Body":33}))) = true := by decide +kernel

-- Non-escaping ordinary output follows from the actual static-preservation
-- theorem, without requiring a native snapshot value specification.
example (fuel : Nat) (memory after : Memory) (pl pr : Pointer) (cell : Cell) (cost : Cost)
    (hargs : FieldsTyped memory [.shared pl, .shared pr] [.shared (.adt .word), .shared (.adt .word)])
    (hr : MemoSource.Heap.run MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost)) :
    Borrow.Unborrowed after cell :=
  (MemoSource.Types.original_run_unborrowed fuel .concatenate (by decide) memory _ cell after cost hargs hr).2.2

-- Generic Box can contain a shared loan; it is excluded from that corollary.
example : ¬Borrow.Unborrowed [.node .word 0 [], .shared ⟨0, []⟩] (.owned 1) := by
  intro h
  cases h with
  | owned hr child =>
    change some (Cell.shared ⟨0, []⟩) = some _ at hr
    cases hr
    cases child

end MemoTypeTests
