import SubtreeProofs.Rust.LookupSourceFrontend

/-! Reader/control discriminator fragments. These are deliberately small JSON
fragments, not claimed to be complete well-typed LLBC crates. The separate
certificate module checks actual pinned extractions, including the mutant. -/

namespace LookupFrontendTests

open Lean
open SubtreeProofs.Rust.LookupSource

private def ctx : Frontend.Context :=
  ⟨[(1, .word), (2, .tuple), (3, .entry), (4, .embedding), (5, .table), (6, .optional)],
    [(10, .copyWord), (11, .compare), (12, .copyResult), (13, .lookup), (14, .boxNew)], 16⟩

private def rejected (result : Except String α) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : Frontend.rootName
    [json% {"Ident":["verified_ordered_core",0]}, json% {"Ident":["words_equal",0]}] =
    .ok (some .compare) := by decide +kernel

-- A nested same-name helper cannot satisfy a root declaration or alias its ID.
example : Frontend.rootName
    [json% {"Ident":["verified_ordered_core",0]}, json% {"Ident":["nested",0]},
      json% {"Ident":["words_equal",0]}] = .ok none := by decide +kernel

example : Frontend.place ctx 4 (json% {"kind":{"Local":15}}) = .ok (.local 15) := by rfl

example : rejected (Frontend.place ctx 4 (json% {"kind":{"Local":16}})) = true := by decide +kernel

example : rejected (Frontend.declarations (json% [{"def_id":1},{"def_id":1}])) = true := by decide +kernel

example : rejected (Frontend.context (json% {"type_decls":[
    {"def_id":1,"item_meta":{"name":[{"Ident":["verified_ordered_core",0]},
      {"Ident":["BalancedWord",0]}]}},
    {"def_id":2,"item_meta":{"name":[{"Ident":["verified_ordered_core",0]},
      {"Ident":["BalancedWord",0]}]}}],"fun_decls":[]})) = true := by decide +kernel

-- In-bounds slot numbers alone do not validate a reordered local table.
example : rejected (Frontend.function ctx [(.copyWord, json% {
    "signature":{"inputs":[{"Untagged":{"Ref":[null,
      {"Untagged":{"Adt":{"id":1}}},"Shared"]}}],
      "output":{"Untagged":{"Adt":{"id":1}}}},
    "body":{"Structured":{"locals":{"arg_count":1,
      "locals":[{"index":0},{"index":0}]},
      "body":{"statements":[{"kind":"Return"}]}}}})] 8 .copyWord) = true := by
  decide +kernel

example : rejected (Frontend.operand ctx 8 (json% {"Move":{"kind":{"Projection":[
    {"kind":{"Local":1}},"Deref"]}}})) = true := by decide +kernel

example : rejected (Frontend.rvalue ctx 8 (json% {"Use":[
    {"Const":{"Untagged":[{"Bool":true},{"Untagged":{"Scalar":"Bool"}}]}},"No"]})) = true := by
  decide +kernel

example : rejected (Frontend.rvalue ctx 8 (json% {"Ref":{
    "kind":"Mut", "place":{"kind":{"Local":1}},
    "ptr_metadata":{"Const":{"Untagged":[{"Adt":[null,[]]},
      {"Untagged":{"Adt":{"id":2}}}]}}}})) = true := by decide +kernel

example : rejected (Frontend.rvalue ctx 8 (json% {"Aggregate":[
    {"Adt":[{"id":1},0,0]},[]]})) = true := by decide +kernel

example : rejected (Frontend.action ctx 8 "Call" (json% {
    "on_unwind":{"statements":[]}, "dest":{"kind":{"Local":0}},
    "call":{"safety":"Inherit","func":{"Regular":{"kind":{"Fun":99}}},
      "args":[{"Move":{"kind":{"Local":1}}}]}})) = true := by decide +kernel

example : rejected (Frontend.sequence ctx 8 [json% {"kind":"Return"},
    json% {"kind":{"StorageDead":1}}]) = true := by decide +kernel

example : rejected (Frontend.sequence ctx 8 [json% {"kind":{"Assert":{}}}]) = true := by
  decide +kernel

example : Control.lowerDispatch [(.boolean true, 0)] (some 0) = none := rfl
example : Control.lowerDispatch [(.boolean true, 2)] (some 0) = none := rfl
example : Control.lowerDispatch [(.boolean true, 0), (.boolean false, 1)] (some 0) = none := rfl

private def selected : Control.Block :=
  .switch (.value (.copy (.local 1))) [(.boolean true, 1)] (some 0)
    (.step (.assign 0 (.use (.boolean false))) .done)
    (.step (.assign 0 (.use (.boolean true))) .ret)
    (.step (.assign 0 (.use (.boolean false))) .ret)

private def env (value : Bool) : Env := fun slot =>
  if slot = 1 then some (.boolean value) else none

private def observe (result : Option (Outcome × Cost)) : Option (Bool × Nat) :=
  match result with
  | some (.returned (.boolean value), cost) => some (value, cost.steps)
  | _ => none

-- Index 1 selects the second source arm. Its early return skips the common
-- continuation; index 0 falls through and must execute that continuation.
example : observe (Control.exec (fun _ _ => none) selected (env true)) = some (true, 5) := by
  decide +kernel

example : observe (Control.exec (fun _ _ => none) selected (env false)) = some (false, 7) := by
  decide +kernel

end LookupFrontendTests
