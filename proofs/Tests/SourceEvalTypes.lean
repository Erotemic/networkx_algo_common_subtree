import SubtreeProofs.Rust.SourceEvalTypeCertificate
import SubtreeProofs.Rust.SourceEvalTypePrimitives

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource SubtreeProofs.Rust.LookupSource.Heap
open SubtreeProofs.Rust.LookupSource.Partial

-- Consumers of the checked actual evaluator and public-entry declarations.
example : ∃ locals,
    locals.take 4 = [.tuple [.adt .optional, .adt .table], .shared (.adt .word), .shared (.adt .word), .adt .table] ∧
    SourceEval.Types.CodeConstraints locals (.tuple [.adt .optional, .adt .table])
      (SourceEval.Certificate.original.body .evaluate) := by
  exact SourceEval.TypeReader.Certificate.original_boundaries .evaluate (by decide +kernel)

example : ∃ locals,
    locals.take 3 = [.adt .optional, .shared (.adt .word), .shared (.adt .word)] ∧
    SourceEval.Types.CodeConstraints locals (.adt .optional) (SourceEval.Certificate.original.body .maximum) := by
  exact SourceEval.TypeReader.Certificate.original_boundaries .maximum (by decide +kernel)

-- Scalar options have their own field type, independently of witness options.
example : SourceEval.TypeReader.scoreLayoutCheck ⟨.optional, 0, []⟩ = true := by decide +kernel
example : SourceEval.TypeReader.scoreLayoutCheck ⟨.optional, 1, [.u32]⟩ = true := by decide +kernel
example : SourceEval.TypeReader.scoreLayoutCheck ⟨.optional, 1, [.adt .embedding]⟩ = false := by decide +kernel
example : Shape .optional 1 [.u32] (.option .u32) := .optionSome _
example : ¬ Shape .optional 1 [.adt .embedding] (.option .u32) := by
  intro h
  cases h

example : SourceEval.Types.checkExpr [] (.option .u32) (.aggregate .optional 1 [.number 4294967295]) = true := by
  decide +kernel
example : SourceEval.Types.checkExpr [] (.adt .optional) (.aggregate .optional 1 [.number 4294967295]) = false := by
  decide +kernel
example : SourceEval.Types.inferOperand [] (.number 4294967296) = none := by decide +kernel

-- An owned field can move out of a Box; a shared referent cannot be moved out.
example : SourceEval.Types.inferOperand [.owned (.adt .embedding)]
    (.move (.field (.deref (.local 0)) none 0)) = some (.adt .word) := by
  simp [SourceEval.Types.inferOperand, SourceEval.Types.inferMovePlace, SourceTypes.fieldType, SourceTypes.constructorFields]
example : SourceEval.Types.inferOperand [.shared (.adt .embedding)]
    (.move (.field (.deref (.local 0)) none 0)) = none := by decide +kernel
example : SourceEval.Types.inferOperand [.shared (.adt .embedding)]
    (.copy (.field (.deref (.local 0)) none 1)) = some .u32 := by
  simp [SourceEval.Types.inferOperand, SourceTypes.inferPlace, SourceTypes.deref, SourceTypes.fieldType, SourceTypes.constructorFields, SourceTypes.copyable]

-- A live partially moved aggregate keeps its tag and typed remaining fields.
example (result : verified_ordered_core.CommonEmbedding) (table : verified_ordered_core.MemoTable) :
    ∃ remaining,
      (Slot.ofValue (.node .tuple 0 [encodeResult result, encodeTable table])).take [.field none 0] =
        some (encodeResult result, remaining) ∧
      SlotTyped remaining (.tuple [.adt .embedding, .adt .table]) ∧
      SnapshotTyped (encodeResult result) (.adt .embedding) := by
  let remaining := Slot.node .tuple 0 [.empty, Slot.ofValue (encodeTable table)]
  have hm : (Slot.ofValue (.node .tuple 0 [encodeResult result, encodeTable table])).take [.field none 0] =
      some (encodeResult result, remaining) := by
    simp only [Slot.ofValue, ofFields, Slot.take, Option.all_none, ite_true,
      List.getElem?_cons_zero, bind, Option.bind, Slot.materialize_ofValue, List.set_cons_zero]
    rfl
  have hp : SlotTyped (Slot.ofValue (.node .tuple 0 [encodeResult result, encodeTable table]))
      (.tuple [.adt .embedding, .adt .table]) :=
    ofValue_typed (.node (.tuple _) (.cons (result_typed result) (.cons (table_typed table) .nil)))
  have ht := hp.take [.field none 0] (target := .adt .embedding) (by simp [inferPath, SourceTypes.fieldType]) hm
  exact ⟨remaining, hm, ht.2, ht.1⟩

-- Every successful typed primitive action preserves the full declared partial
-- local invariant, including holes and live-drop clears. No type assumption is
-- silently replaced by ordinary scalar boundedness.
example (call : SourceEval.Calls) (hc : SourceEval.Types.CallsTyped call) (locals : List Ty)
    (state after : SourceEval.State) (work : SourceEval.Cost) (instruction : SourceEval.Action)
    (hs : LocalsTyped locals state) (ht : SourceEval.Types.ActionConstraints locals instruction)
    (hr : SourceEval.action call state instruction = some (after, work)) : LocalsTyped locals after :=
  SourceEval.Types.action_typed hc hs instruction ht hr
