module

public import SubtreeProofs.Rust.SourceCallingNoCalls
public import SubtreeProofs.Rust.SourceChoiceTotality

/-! Constructed choice execution transfers to any callee implementation and
to the actual recursive dispatcher with one unit of call fuel. Input ownership,
actual suspended loan separation and protected-read membership stay explicit;
no successful recursive run or expected final world is supplied. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem invoke_total_with (callee : Derived.Callees) {world : World} {callers : List Activation} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (first second : CommonEmbedding) (firstCell secondCell : Cell)
    (firstReadable : Readable world.memory world.live firstCell (encodeResult first))
    (secondReadable : Readable world.memory world.live secondCell (encodeResult second))
    {inputOwners external : List Nat} {previous : Resources} (view : Callers world callers previous)
    (input : FieldsFootprint world.memory [firstCell, secondCell] inputOwners)
    (frame : OwnerFrame world (inputOwners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (inputOwners ++ (callerOwners world callers ++ external)))
    (transfer : List.Disjoint inputOwners previous.loans) (protectedReads : guards ⊆ previous.reads) :
    ∃ final packet,
      Calling.guardedInvoke callee callers guards CallingCertificate.originalChoice world
        [(firstCell, encodeResult first), (secondCell, encodeResult second)] = some (final, packet, cost first second) ∧
      packet.2 = encodeResult (OrderedSolver.selectResult first second) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      ∃ output, Footprint final.memory packet.1 output ∧
        OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (output ++ (callerOwners final callers ++ external)) := by
  obtain ⟨final, packet, run, rest⟩ := invoke_total 0 0 hw hc first second firstCell secondCell
    firstReadable secondReadable view input frame covered transfer protectedReads
  rw [Calling.guardedInvoke_noCalls (Helpers.callee 0 0) callee callers guards CallingCertificate.originalChoice
    (by rw [CallingCertificate.originalChoice_spec.2.2]; decide +kernel)] at run
  exact ⟨final, packet, run, rest⟩

end SubtreeProofs.Rust.SourceEval.Choice

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem run_choice_total (program : List TypeReader.Definition)
    (found : program.find? (fun decl => decl.source.function == .chooseLonger) = some CallingCertificate.originalChoice)
    (budget fuel : Nat) {world : World} {callers : List Activation} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (first second : CommonEmbedding) (firstCell secondCell : Cell)
    (firstReadable : Readable world.memory world.live firstCell (encodeResult first))
    (secondReadable : Readable world.memory world.live secondCell (encodeResult second))
    {inputOwners external : List Nat} {previous : Resources} (view : Callers world callers previous)
    (input : FieldsFootprint world.memory [firstCell, secondCell] inputOwners)
    (frame : OwnerFrame world (inputOwners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (inputOwners ++ (callerOwners world callers ++ external)))
    (transfer : List.Disjoint inputOwners previous.loans) (protectedReads : guards ⊆ previous.reads) :
    ∃ final packet,
      run program budget (fuel + 1) world guards callers .chooseLonger
        [(firstCell, encodeResult first), (secondCell, encodeResult second)] = some (final, packet, Choice.cost first second) ∧
      packet.2 = encodeResult (OrderedSolver.selectResult first second) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      ∃ output, Footprint final.memory packet.1 output ∧
        OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (output ++ (callerOwners final callers ++ external)) := by
  obtain ⟨final, packet, execute, rest⟩ := Choice.invoke_total_with (run program budget fuel)
    hw hc first second firstCell secondCell firstReadable secondReadable view input frame covered transfer protectedReads
  exact ⟨final, packet, by simpa only [run, interpreted, ite_true, found, bind, Option.bind] using execute, rest⟩

theorem original_choice_total (budget fuel : Nat) {world : World} {callers : List Activation} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (first second : CommonEmbedding) (firstCell secondCell : Cell)
    (firstReadable : Readable world.memory world.live firstCell (encodeResult first))
    (secondReadable : Readable world.memory world.live secondCell (encodeResult second))
    {inputOwners external : List Nat} {previous : Resources} (view : Callers world callers previous)
    (input : FieldsFootprint world.memory [firstCell, secondCell] inputOwners)
    (frame : OwnerFrame world (inputOwners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (inputOwners ++ (callerOwners world callers ++ external)))
    (transfer : List.Disjoint inputOwners previous.loans) (protectedReads : guards ⊆ previous.reads) :
    ∃ final packet,
      original budget (fuel + 1) world guards callers .chooseLonger
        [(firstCell, encodeResult first), (secondCell, encodeResult second)] = some (final, packet, Choice.cost first second) ∧
      packet.2 = encodeResult (OrderedSolver.selectResult first second) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      ∃ output, Footprint final.memory packet.1 output ∧
        OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (output ++ (callerOwners final callers ++ external)) :=
  run_choice_total _ CallingCertificate.choice_lookup budget fuel hw hc first second firstCell secondCell
    firstReadable secondReadable view input frame covered transfer protectedReads

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
