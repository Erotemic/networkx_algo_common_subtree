import SubtreeProofs.Rust.MemoSourceRefinement

/-! The complete actual source certificate is imported above. JSON examples
below are focused discriminator fragments, not compiled Rust mutations. -/

namespace MemoSourceTests

open Lean SubtreeProofs.Rust
open LookupSource
open verified_ordered_core

private def ctx : MemoSource.Frontend.Context :=
  ⟨⟨[(1, .word), (2, .table), (3, .embedding), (4, .tuple)], [], 16⟩,
    [(10, .copyWord), (11, .copyResult), (12, .concatenate), (13, .insert), (14, .boxNew)]⟩

private def rejected (value : Except String α) : Bool :=
  match value with | .error _ => true | .ok _ => false

example : MemoSource.Frontend.rootName [json% {"Ident":["verified_ordered_core",0]},
    json% {"Ident":["memo_insert",0]}] = .ok (some .insert) := by decide +kernel
example : MemoSource.Frontend.rootName [json% {"Ident":["verified_ordered_core",0]},
    json% {"Ident":["nested",0]}, json% {"Ident":["memo_insert",0]}] = .ok none := by decide +kernel

private def word : Json := json% {"Untagged":{"Ref":[null,{"Untagged":{"Adt":{"id":1}}},"Shared"]}}
private def result : Json := json% {"Untagged":{"Ref":[null,{"Untagged":{"Adt":{"id":3}}},"Shared"]}}

-- An owned table is required by insertion; a reference would change transfer semantics.
example : (MemoSource.Frontend.signature ctx .insert (json% {"signature":{
    "inputs":[{"Untagged":{"Adt":{"id":2}}},$(word),$(word),$(result)],
    "output":{"Untagged":{"Adt":{"id":2}}}}})).isOk = true := by decide +kernel
example : rejected (MemoSource.Frontend.signature ctx .insert (json% {"signature":{
    "inputs":[{"Untagged":{"Ref":[null,{"Untagged":{"Adt":{"id":2}}},"Shared"]}},$(word),$(word),$(result)],
    "output":{"Untagged":{"Adt":{"id":2}}}}})) = true := by decide +kernel

-- The reusable call parser uses the new function set's four-argument insertion arity.
example : rejected (MemoSource.Frontend.action ctx ctx.common 32 "Call" (json% {
    "on_unwind":{"statements":[]}, "dest":{"kind":{"Local":0}},
    "call":{"safety":"Inherit","func":{"Regular":{"kind":{"Fun":13}}},
      "args":[{"Move":{"kind":{"Local":1}}}]}})) = true := by decide +kernel
example : (MemoSource.Frontend.action ctx ctx.common 32 "Call" (json% {
    "on_unwind":{"statements":[]}, "dest":{"kind":{"Local":0}},
    "call":{"safety":"Inherit","func":{"Regular":{"kind":{"Fun":13}}},
      "args":[{"Move":{"kind":{"Local":1}}},{"Move":{"kind":{"Local":2}}},
        {"Move":{"kind":{"Local":3}}},{"Move":{"kind":{"Local":4}}}]}})).isOk = true := by decide +kernel

private def one : BalancedWord := .Pair .Empty .Empty
private def witness : CommonEmbedding := ⟨one, 77#u32⟩
private def table : MemoTable := .Entry ⟨one, .Empty, witness⟩ .Empty

-- No soundness premise is imposed on stored witnesses or the inserted score.
example : ∃ cost, MemoSource.sourceRun MemoSource.Certificate.original.body 5 .insert
      [encodeTable table, .reference (encodeWord one), .reference (encodeWord .Empty), .reference (encodeResult witness)] =
    some (encodeTable (.Entry ⟨one, .Empty, witness⟩ table), cost) ∧
    verified_ordered_core.memo_insert table one .Empty witness = .ok (.Entry ⟨one, .Empty, witness⟩ table) ∧
    cost.events = MemoSource.insertEvents one .Empty witness :=
  MemoSource.insert_checked table one .Empty witness 5 (by decide +kernel)

example : (MemoSource.insertEvents one .Empty witness).allocations = 6 := by decide +kernel
example : (MemoSource.insertEvents one .Empty witness).copyNodes = 7 := by decide +kernel
example : (MemoSource.concatenateEvents one one).allocations = 4 := by decide +kernel
example : (MemoSource.concatenateEvents one one).copyNodes = 4 := by decide +kernel

example : ∃ cost, MemoSource.sourceRun MemoSource.Certificate.original.body 5 .concatenate
      [.reference (encodeWord one), .reference (encodeWord one)] =
    some (encodeWord (OrderedSolver.appendWord one one), cost) ∧
    verified_ordered_core.concatenate one one = .ok (OrderedSolver.appendWord one one) ∧
    cost.events = MemoSource.concatenateEvents one one :=
  MemoSource.concatenate_checked one one 5 (by decide +kernel)

-- Exhausted fuel fails explicitly; it cannot certify successful work with zero cost.
example : MemoSource.run MemoSource.Program.body 0 .insert [] = none := rfl

end MemoSourceTests
