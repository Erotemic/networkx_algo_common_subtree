module

public import SubtreeProofs.Rust.SourceOwnerInvoke
public import SubtreeProofs.Rust.SourceEvalTypedRecursive

/-! Complete global owner resources for successful actual recursive execution.
All eight concrete helpers and parsed choice/evaluator/maximum invocations are
discharged by fuel induction, retaining the real suspended stack. Independent
input types derive the selected call domains; physical success stays explicit. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem run_owns (program : List TypeReader.Definition) (aligned : Aligned program) (budget fuel : Nat) :
    Derived.CallsOwn (run program budget fuel) := by
  induction fuel with
  | zero =>
    intro world guards callers function packets final packet cost owners external hw hc hp hl ht ho hf covered h
    cases h
  | succ fuel ih =>
    intro world guards callers function packets final packet cost owners external hw hc hp hl hd ho hf covered h
    have respects := run_typed_respects program aligned budget fuel
    by_cases hi : interpreted function = true
    · simp only [run, hi, ite_true] at h
      cases found : program.find? (fun decl => decl.source.function == function) with
      | none => simp [found] at h
      | some decl =>
        simp only [found, Bind.bind, Option.bind] at h
        have predicate := List.find?_some (p := fun (entry : TypeReader.Definition) => entry.source.function == function) found
        have functionEq : decl.source.function = function := beq_iff_eq.mp predicate
        obtain ⟨types, ty, argsTyped, outputType⟩ := hd
        have standard := Types.callOutput_standard (interpreted_nonintrinsic hi).1 outputType
        rw [standard.1] at argsTyped
        have typed : SnapshotFieldsTyped (packets.map Prod.snd) (Types.inputs decl.source.function) := by
          simpa only [functionEq] using argsTyped
        have ready := Calling.invoke_typed_ready respects (Types.original_run_typed fuel) decl hw hc hp typed
        exact Calling.guardedInvoke_owner_resources respects ih decl hw hc hp ho hf covered ready h
    · exact Helpers.callee_owns (fuel + 1) budget world guards callers function packets final packet cost owners external
        hw hc hp hl hd ho hf covered (by simpa only [run, hi, Bool.false_eq_true, ite_false] using h)

theorem original_owns (budget fuel : Nat) : Derived.CallsOwn (original budget fuel) :=
  run_owns _ CallingCertificate.original_codes budget fuel

theorem original_evaluate_owned_refines (budget fuel : Nat) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {owners external : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2) (hl : AliveOn world.live guards)
    (left right : BalancedWord) (table : MemoTable)
    (hi : packets.map Prod.snd = [.reference (encodeWord left), .reference (encodeWord right), encodeTable table])
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (hf : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (h : original budget fuel world guards callers .evaluate packets = some (final, packet, cost)) :
    ∃ result output outputOwners, packet.2 = Evaluator.encodeOutput result output ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      Evaluator.Evaluation fuel left right table result output cost ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      Footprint final.memory packet.1 outputOwners ∧
      OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external)) := by
  obtain ⟨result, output, value, native, evaluation, readable, wellFormed, kept⟩ :=
    original_evaluate_typed_refines budget fuel hw hc hp hl left right table hi h
  have typed : SnapshotFieldsTyped (packets.map Prod.snd) (Types.inputs .evaluate) := by
    rw [hi]
    exact .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed table) .nil))
  have outputType : Types.callOutput .evaluate (Types.inputs .evaluate) = some (Types.output .evaluate) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, SourceTypes.sameList_refl, ite_true]
  obtain ⟨outputOwners, footprint, frame, coverage⟩ := original_owns budget fuel world guards callers .evaluate packets final packet cost owners external
    hw hc hp hl ⟨_, _, typed, outputType⟩ ho hf covered h
  exact ⟨result, output, outputOwners, value, native, evaluation, readable, wellFormed, kept, footprint, frame, coverage⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
