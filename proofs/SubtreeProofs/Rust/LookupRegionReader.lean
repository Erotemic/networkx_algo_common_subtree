module

public import SubtreeProofs.Rust.LookupRegionTypes
public import SubtreeProofs.Rust.LookupTypeAnnotations

/-! Region-bearing annotations for the supported pinned source type forms.
Successful results carry both exact old-type erasure and binder scope proofs. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader

open Lean Frontend

def region (scope : Scope) (json : Json) : Read {value : Region // Bound scope value} := do
  let (constructor, payload) ← tag json
  match hs : scope with
  | .signature count =>
    if constructor != "Var" then throw "signature region variable required"
    let (constructor, payload) ← tag payload
    if constructor != "Free" then throw "higher region binder unsupported"
    let index ← payload.getNat?
    if hi : index < count then pure ⟨.free index, by simpa only [hs, Bound] using hi⟩ else throw "unbound signature region"
  | .body count =>
    if constructor != "Body" then throw "body existential region required"
    let index ← payload.getNat?
    if hi : index < count then pure ⟨.body index, by simpa only [hs, Bound] using hi⟩ else throw "unbound body region"

mutual
  def attach (scope : Scope) : Nat → (expected : Heap.Ty) → Json → Read (Checked scope expected)
    | 0, _, _ => throw "region annotation budget exceeded"
    | _ + 1, .boolean, _ => pure ⟨.boolean, by simp only [erase], .boolean⟩
    | _ + 1, .u32, _ => pure ⟨.u32, by simp only [erase], .u32⟩
    | _ + 1, .adt kind, _ => pure ⟨.adt kind, by simp only [erase], .adt kind⟩
    | _ + 1, .option _, _ => throw "parameterized options require the expanded region profile"
    | fuel + 1, .shared inner, json => do
      let data ← field (← field json "Untagged") "Ref"
      match ← array data with
      | [rawRegion, rawInner, _] =>
        let r ← region scope rawRegion
        let child ← attach scope fuel inner rawInner
        pure ⟨.shared r.val child.type, by simp only [erase, child.erases], .shared r.property child.wf⟩
      | _ => throw "invalid region-bearing shared type"
    | fuel + 1, .owned inner, json => do
      let data ← field (← field json "Untagged") "Adt"
      match ← array (← field (← field data "generics") "types") with
      | [rawInner] =>
        let child ← attach scope fuel inner rawInner
        pure ⟨.owned child.type, by simp only [erase, child.erases], .owned child.wf⟩
      | _ => throw "invalid region-bearing Box type"
    | fuel + 1, .tuple types, json => do
      let data ← field (← field json "Untagged") "Adt"
      let fields ← attachFields scope fuel types (← array (← field (← field data "generics") "types"))
      pure ⟨.tuple fields.types, by simp only [erase, fields.erases], .tuple fields.wf⟩
  termination_by fuel _ _ => fuel

  def attachFields (scope : Scope) : Nat → (expected : List Heap.Ty) → List Json → Read (CheckedFields scope expected)
    | 0, _, _ => throw "region field annotation budget exceeded"
    | _ + 1, [], [] => pure ⟨[], by simp only [eraseList], .nil⟩
    | fuel + 1, first :: rest, raw :: raws => do
      let head ← attach scope fuel first raw
      let tail ← attachFields scope fuel rest raws
      pure ⟨head.type :: tail.types, by simp only [eraseList, head.erases, tail.erases], .cons head.wf tail.wf⟩
    | _, _, _ => throw "region annotation field count mismatch"
  termination_by fuel _ _ => fuel
end

structure Annotation (scope : Scope) where
  erased : Heap.Ty
  checked : Checked scope erased

def annotation (ctx : TypeReader.Context) (scope : Scope) (json : Json) : Read (Annotation scope) := do
  let erased ← TypeReader.type ctx none 64 json
  pure ⟨erased, ← attach scope 128 erased json⟩

structure Annotations (scope : Scope) where
  erased : List Heap.Ty
  checked : CheckedFields scope erased

def annotations (ctx : TypeReader.Context) (scope : Scope) (jsons : List Json) : Read (Annotations scope) := do
  let erased ← jsons.mapM (TypeReader.type ctx none 64)
  pure ⟨erased, ← attachFields scope 512 erased jsons⟩

end SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader
