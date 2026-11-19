module

public import SubtreeProofs.Rust.SourceEvalRecursiveRefinement
public import SubtreeProofs.Rust.SourceEvalTypedCalling
public import SubtreeProofs.Rust.SourceEvalHelperReflection

/-! Recursive source/cost correspondence from independently typed actual inputs.
All local call input conditions are derived along actual execution. The earlier
native path-readiness premise is unnecessary for this stronger conditional
refinement; existence of successful physical execution remains an obligation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap

theorem callee_typed_respects (fuel budget : Nat) :
    Derived.CallsRespect (callee fuel budget) (SourceEval.run SourceEval.Certificate.original.body fuel) Derived.TypedReady := by
  intro world guards suspended function packets final packet cost hw hp hc hl hd hrun
  obtain ⟨types, ty, ht, _⟩ := hd
  exact callee_bounded_respects fuel budget world guards suspended function packets final packet cost
    hw hp hc hl ht.bounded hrun

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource Heap LookupSource.Partial LookupSource.Partial.Addressed Storage verified_ordered_core

theorem run_typed_respects (program : List TypeReader.Definition) (aligned : Aligned program) (budget fuel : Nat) :
    Derived.CallsRespect (run program budget fuel) (SourceEval.run Certificate.original.body fuel) Derived.TypedReady := by
  induction fuel with
  | zero =>
    intro world guards callers function packets final packet cost hw hp hc hl hd h
    cases h
  | succ fuel ih =>
    intro world guards callers function packets final packet cost hw hp hc hl hd h
    by_cases hi : interpreted function = true
    · simp only [run, hi, ite_true] at h
      cases hf : program.find? (fun decl => decl.source.function == function) with
      | none => simp [hf] at h
      | some decl =>
        simp only [hf, Bind.bind, Option.bind] at h
        have hpredicate := List.find?_some (p := fun (entry : TypeReader.Definition) => entry.source.function == function) hf
        have hfunction : decl.source.function = function := beq_iff_eq.mp hpredicate
        have hcode := aligned decl (List.mem_of_find?_eq_some hf)
        have hordinary := interpreted_nonintrinsic (function := decl.source.function) (by simpa only [hfunction] using hi)
        obtain ⟨types, ty, hargs, hout⟩ := hd
        have standard := Types.callOutput_standard (interpreted_nonintrinsic hi).1 hout
        rw [standard.1] at hargs
        have hargs' : SnapshotFieldsTyped (packets.map Prod.snd) (Types.inputs decl.source.function) := by
          simpa only [hfunction] using hargs
        have ready := Calling.invoke_typed_ready ih (Types.original_run_typed fuel) decl hw hc hp hargs'
        have result := Calling.guardedInvoke_spec ih decl hcode hordinary.1 hordinary.2 hw hc hp ready h
        simpa only [hfunction] using result
    · exact Helpers.callee_typed_respects (fuel + 1) budget world guards callers function packets final packet cost hw hp hc hl hd
        (by simpa only [run, hi, Bool.false_eq_true, ite_false] using h)

theorem original_typed_respects (budget fuel : Nat) :
    Derived.CallsRespect (original budget fuel) (SourceEval.run Certificate.original.body fuel) Derived.TypedReady :=
  run_typed_respects _ CallingCertificate.original_codes budget fuel

theorem original_typed_spec (budget fuel : Nat) {world final : World} {callers : List Activation} {guards : List Nat}
    {function : Function} {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {types : List Ty} {ty : Ty}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (hl : AliveOn world.live guards)
    (ht : SnapshotFieldsTyped (packets.map Prod.snd) types) (hout : Types.callOutput function types = some ty)
    (h : original budget fuel world guards callers function packets = some (final, packet, cost)) :
    SourceEval.run Certificate.original.body fuel function (packets.map Prod.snd) = some (packet.2, cost) ∧
      SnapshotTyped packet.2 ty ∧ Readable final.memory final.live packet.1 packet.2 ∧
      final.WellFormed ∧ Preserves world final guards := by
  obtain ⟨hs, hr, hf, hk⟩ := original_typed_respects budget fuel world guards callers function packets final packet cost
    hw hp hc hl ⟨types, ty, ht, hout⟩ h
  exact ⟨hs, Types.original_run_typed fuel function _ types _ cost ty ht hout hs, hr, hf, hk⟩

theorem original_evaluate_typed_refines (budget fuel : Nat) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (hl : AliveOn world.live guards)
    (left right : BalancedWord) (table : MemoTable)
    (hi : packets.map Prod.snd = [.reference (encodeWord left), .reference (encodeWord right), encodeTable table])
    (h : original budget fuel world guards callers .evaluate packets = some (final, packet, cost)) :
    ∃ result output, packet.2 = Evaluator.encodeOutput result output ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      Evaluator.Evaluation fuel left right table result output cost ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards := by
  have ht : SnapshotFieldsTyped (packets.map Prod.snd) (Types.inputs .evaluate) := by
    rw [hi]
    exact .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))
  have ho : Types.callOutput .evaluate (Types.inputs .evaluate) = some (Types.output .evaluate) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, SourceTypes.sameList_refl, ite_true]
  obtain ⟨hs, _, hr, hf, hk⟩ := original_typed_spec budget fuel hw hc hp hl ht ho h
  rw [hi] at hs
  obtain ⟨result, output, he, evaluation⟩ := Evaluator.evaluate_refines left right table fuel hs
  exact ⟨result, output, he, evaluation.native, evaluation, hr, hf, hk⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
