import SubtreeProofs.Rust.LookupTypeAnnotations
import SubtreeProofs.Rust.LookupFrameChecker

/-! Small typed source fragments and static constraints. They are not claimed
to be complete LLBC crates or lifetime-well-formed Rust programs. -/

namespace LookupSourceTypeTests

open Lean SubtreeProofs.Rust.LookupSource Heap SourceTypes

private def ctx : TypeReader.Context :=
  ⟨⟨[(1, .word), (2, .table), (3, .entry), (4, .embedding), (5, .optional), (6, .tuple)],
      [(10, .copyWord), (11, .compare), (12, .copyResult), (13, .lookup), (14, .boxNew)], 0⟩, 7⟩

private def rejected (value : Except String α) : Bool :=
  match value with | .error _ => true | .ok _ => false

example : SourceTypes.same (.shared (.owned (.adt .word))) (.shared (.owned (.adt .word))) = true := by
  decide +kernel

example : SourceTypes.same (.tuple [.shared (.adt .word), .u32]) (.tuple [.shared (.adt .word), .boolean]) = false := by
  decide +kernel

example : (TypeReader.type ctx none 8 (json% {"Untagged":{"Adt":{"id":7,"builtin":"Box",
    "generics":{"types":[{"Untagged":{"Adt":{"id":1,"builtin":null,
      "generics":{"types":[],"regions":[],"const_generics":[],"trait_refs":[]}}}}],
      "regions":[],"const_generics":[],"trait_refs":[]}}}})).map (SourceTypes.same (.owned (.adt .word))) = .ok true := by
  decide +kernel

example : rejected (TypeReader.type ctx none 8 (json% {"Untagged":{"Adt":{"id":99,"builtin":"Box",
    "generics":{"types":[{"Untagged":{"Scalar":"Bool"}}],
      "regions":[],"const_generics":[],"trait_refs":[]}}}})) = true := by decide +kernel

example : rejected (TypeReader.type ctx none 8 (json% {"Untagged":{"Ref":[{"Body":0},
    {"Untagged":{"Scalar":"Bool"}},"Mut"]}})) = true := by decide +kernel

example : rejected (TypeReader.type ctx none 8 (json% {"Untagged":{"Scalar":{"Integer":{"Signed":"I32"}}}})) = true := by
  decide +kernel

example : rejected (TypeReader.type ctx none 8 (json% {"Untagged":{"Adt":{"id":5,"builtin":null,
    "generics":{"types":[{"Untagged":{"Adt":{"id":1,"builtin":null,
      "generics":{"types":[],"regions":[],"const_generics":[],"trait_refs":[]}}}}],
      "regions":[],"const_generics":[],"trait_refs":[]}}}})) = true := by decide +kernel

-- The control reader ignores this false type annotation; the new pass rejects it.
example : Frontend.place { ctx.source with localCount := 1 } 4
    (json% {"kind":{"Local":0},"ty":{"Untagged":{"Scalar":"Bool"}}}) = .ok (.local 0) := rfl

example : rejected (TypeReader.placeAnnotations ctx [.adt .word] 4
    (json% {"kind":{"Local":0},"ty":{"Untagged":{"Scalar":"Bool"}}})) = true := by decide +kernel

example : rejected (TypeReader.operandAnnotations ctx [] 8
    (json% {"Const":{"Untagged":[{"Bool":true},{"Untagged":{"Scalar":{"Integer":{"Unsigned":"U32"}}}}]}})) = true := by
  decide +kernel

example : TypeReader.layoutCheck ⟨.word, 1, [.owned (.adt .word), .owned (.adt .word)]⟩ = true := by decide +kernel
example : TypeReader.layoutCheck ⟨.word, 1, []⟩ = false := by decide +kernel
example : TypeReader.layoutCheck ⟨.word, 1, [.owned (.adt .embedding), .owned (.adt .word)]⟩ = false := by decide +kernel
example : TypeReader.layoutCheck ⟨.embedding, 0, [.adt .word, .boolean]⟩ = false := by decide +kernel
example : TypeReader.layoutCheck ⟨.word, 2, []⟩ = false := by decide +kernel

-- Ownership-class safety alone cannot establish constructor field typing.
private def badWord : Code := .step (.assign 0 (.aggregate .word 1 [.boolean true, .boolean false])) .ret
example : Frame.verify badWord (Frame.initialState 4 []) true (fun _ => false) = true := by decide +kernel
example : checkCode [.adt .word] (.adt .word) badWord = false := by decide +kernel

example : checkCode [.adt .word] (.adt .word) (.step (.assign 0 (.aggregate .word 0 [])) .ret) = true := by
  decide +kernel

example : (callOutput .copyWord [.owned (.adt .word)]).isNone = true := by decide +kernel
example : (fieldType (.adt .word) (some 1) 2).isNone = true := by decide +kernel

-- A Box call's generic argument must match its operand, even when its lowered
-- call and destination have otherwise compatible types.
example : rejected (TypeReader.actionAnnotations ctx [.owned (.adt .word), .adt .word] 8 "Call" (json% {
    "dest":{"kind":{"Local":0},"ty":{"Untagged":{"Adt":{"id":7,"builtin":"Box",
      "generics":{"types":[{"Untagged":{"Adt":{"id":1,"builtin":null,
        "generics":{"types":[],"regions":[],"const_generics":[],"trait_refs":[]}}}}],
        "regions":[],"const_generics":[],"trait_refs":[]}}}}},
    "on_unwind":{"statements":[]},
    "call":{"safety":"Inherit","func":{"Regular":{"kind":{"Fun":14},
      "generics":{"types":[{"Untagged":{"Scalar":"Bool"}}],"regions":[],"const_generics":[],"trait_refs":[]}}},
      "args":[{"Move":{"kind":{"Local":1},"ty":{"Untagged":{"Adt":{"id":1,"builtin":null,
        "generics":{"types":[],"regions":[],"const_generics":[],"trait_refs":[]}}}}}}]}})) = true := by
  decide +kernel

end LookupSourceTypeTests
