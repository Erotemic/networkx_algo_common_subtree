module

public import SubtreeProofs.Rust.SourceCallingBoxOrigin
public import SubtreeProofs.Rust.SourceEvalTypedRecursive

/-! Every successful typed recursive dispatch preserves backward live-Box
provenance and all actual suspended caller reads. No execution result, ownership
separation or cache soundness is assumed beyond the successful run being studied. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource Heap Partial Partial.Addressed Storage

theorem run_boxOrigin (program : List TypeReader.Definition) (aligned : Aligned program) (budget fuel : Nat) :
    Derived.CallsBoxOrigin (run program budget fuel) := by
  induction fuel with
  | zero =>
    intro world guards callers function packets final packet cost hw hc hp hd h
    cases h
  | succ fuel ih =>
    intro world guards callers function packets final packet cost hw hc hp hd h
    have respects := run_typed_respects program aligned budget fuel
    by_cases hi : interpreted function = true
    · simp only [run, hi, ite_true] at h
      cases found : program.find? (fun decl => decl.source.function == function) with
      | none => simp [found] at h
      | some decl =>
        simp only [found, bind, Option.bind] at h
        have predicate := List.find?_some (p := fun (entry : TypeReader.Definition) => entry.source.function == function) found
        have functionEq : decl.source.function = function := beq_iff_eq.mp predicate
        obtain ⟨types, ty, argsTyped, outputType⟩ := hd
        have standard := Types.callOutput_standard (interpreted_nonintrinsic hi).1 outputType
        rw [standard.1] at argsTyped
        have typed : SnapshotFieldsTyped (packets.map Prod.snd) (Types.inputs decl.source.function) := by
          simpa only [functionEq] using argsTyped
        have ready := Calling.invoke_typed_ready respects (Types.original_run_typed fuel) decl hw hc hp typed
        exact Calling.guardedInvoke_boxOrigin respects ih decl hw hc hp ready h
    · exact Helpers.callee_boxOrigin (fuel + 1) budget hw function packets hp hd
        (by simpa only [run, hi, Bool.false_eq_true, ite_false] using h)

theorem original_boxOrigin (budget fuel : Nat) : Derived.CallsBoxOrigin (original budget fuel) :=
  run_boxOrigin _ CallingCertificate.original_codes budget fuel

theorem run_callers_preserved (program : List TypeReader.Definition) (aligned : Aligned program)
    (budget fuel : Nat) {world final : World} {callers : List Activation} {guards : List Nat}
    {function : Function} {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {r : Resources}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : Derived.TypedReady world function packets) (view : Callers world callers r)
    (h : run program budget fuel world guards callers function packets = some (final, packet, cost)) :
    Preserves world final r.reads := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    have respects := run_typed_respects program aligned budget fuel
    by_cases hi : interpreted function = true
    · simp only [run, hi, ite_true] at h
      cases found : program.find? (fun decl => decl.source.function == function) with
      | none => simp [found] at h
      | some decl =>
        simp only [found, bind, Option.bind] at h
        have predicate := List.find?_some (p := fun (entry : TypeReader.Definition) => entry.source.function == function) found
        have functionEq : decl.source.function = function := beq_iff_eq.mp predicate
        obtain ⟨types, ty, argsTyped, outputType⟩ := hd
        have standard := Types.callOutput_standard (interpreted_nonintrinsic hi).1 outputType
        rw [standard.1] at argsTyped
        have typed : SnapshotFieldsTyped (packets.map Prod.snd) (Types.inputs decl.source.function) := by
          simpa only [functionEq] using argsTyped
        have ready := Calling.invoke_typed_ready respects (Types.original_run_typed fuel) decl hw hc hp typed
        simp only [Calling.guardedInvoke, bind, Option.bind_eq_some_iff] at h
        obtain ⟨suspended, scanned, h⟩ := h
        split at h
        · have kept := Calling.invoke_preserves respects decl hw hc hp ready h scanned
          rwa [(scanCallers_spec hc scanned).reads_unique view] at kept
        · cases h
    · have helper : Helpers.callee (fuel + 1) budget world guards callers function packets =
          some (final, packet, cost) := by
        simpa only [run, hi, Bool.false_eq_true, ite_false] using h
      obtain ⟨_, _, _, he, shape⟩ := Helpers.callee_owner_ledger (fuel + 1) budget hw function packets hp hd
        (packetOwners_footprint hp) helper
      have kept := (world.boxSuffix_keeps hw he r.reads).preserves
      rwa [← shape] at kept

theorem original_callers_preserved (budget fuel : Nat)
    {world final : World} {callers : List Activation} {guards : List Nat}
    {function : Function} {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {r : Resources}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : Derived.TypedReady world function packets) (view : Callers world callers r)
    (h : original budget fuel world guards callers function packets = some (final, packet, cost)) :
    Preserves world final r.reads :=
  run_callers_preserved _ CallingCertificate.original_codes budget fuel hw hc hp hd view h

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
