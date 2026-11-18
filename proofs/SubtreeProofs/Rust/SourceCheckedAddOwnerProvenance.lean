module

public import SubtreeProofs.Rust.SourceCallOwnerProvenance
public import SubtreeProofs.Rust.SourceEvalHelperReflection

/-! Actual successful checked-add calls supply their scalar input readiness.
Untouched owner bounds then survive scalar prefixes, including overflow results,
without a desired successful numeric result or a complete parent invocation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

namespace Derived

theorem checkedAdd_ready_of_call {world final : World} {active after : Activation} {callers : List Activation}
    {fuel budget destination : Nat} {args : List Operand} {cost : Cost}
    (ha : active.Valid world)
    (run : call (Recursive.original budget fuel) world active callers .checkedAdd args destination = some (final, after, cost)) :
    ∀ current suspended packets masks, active.scan world = some current → scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world .checkedAdd packets := by
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packets, masks⟩, arguments,
    remainder, _, binding, _, ⟨returned, packet, inner⟩, invoked, _, _, _⟩ := run
  have frame := (Activation.scan_spec ha currentScan).frame
  obtain ⟨_, _, graph, subset, _⟩ := Addressed.operands_spec frame args arguments
  have readable := packets_readable graph (fun address member => frame.alive address (subset member))
  have actualReady : TypedReady world .checkedAdd packets := by
    cases fuel with
    | zero => cases invoked
    | succ fuel =>
      have checked : Helpers.checkedAdd (fuel + 1) world packets = some (returned, packet, inner) := by
        simpa only [Recursive.original, Recursive.run, Recursive.interpreted, Bool.false_eq_true, ite_false,
          Helpers.callee, Helpers.execute] using invoked
      have ready := Helpers.checkedAdd_ready readable checked
      cases ready with
      | checkedAdd left right positive leftBound rightBound =>
        exact ⟨[.u32, .u32], .option .u32, .cons (.number leftBound) (.cons (.number rightBound) .nil),
          by simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]⟩
  intro observed old actual actualMasks scan callerScan' selected
  have currentEq := Option.some.inj (currentScan.symm.trans scan)
  have callersEq := Option.some.inj (callerScan.symm.trans callerScan')
  subst observed old
  have same := Prod.mk.inj (Option.some.inj (arguments.symm.trans selected))
  rw [← same.1]
  exact actualReady

end Derived

namespace Calling

theorem Prefix.checkedAdd_keeps_owner_provenance {fuel budget : Nat} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation} {index bound : Nat}
    (steps : Prefix (Recursive.original budget fuel) callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (bounded : index < active.count)
    (onlyScalar : ∀ function args destination, Action.call function args destination ∈ actions → function = .checkedAdd)
    (safe : actions.all (LocalPreservation.action index) = true)
    (above : LocalOwnersAbove bound world active index) : LocalOwnersAbove bound final after index := by
  induction actions generalizing world active with
  | nil => cases steps; exact above
  | cons act rest ih => cases steps with
    | @cons _ middle _ _ current _ _ _ cost run tail =>
      let code := (act :: rest).foldr Control.Tree.step suffix
      let prepared := active.forgetRefs code
      have valid := Activation.forgetRefs_valid ha code
      have parts := Bool.and_eq_true_iff.mp safe
      have next : current.Valid middle ∧ (∀ caller ∈ callers, caller.Valid middle) ∧ middle.WellFormed ∧
          LocalOwnersAbove bound middle current index := by
        cases act with
        | call function args destination =>
          have same := onlyScalar function args destination (by simp)
          subst function
          have raw := run
          simp only [instruction, bind, Option.bind_eq_some_iff] at raw
          obtain ⟨⟨ending, endingActive, work⟩, called, last⟩ := raw
          cases last
          have ready := Derived.checkedAdd_ready_of_call valid called
          have spec := Derived.call_spec (Recursive.original_typed_respects budget fuel) valid hc hw .checkedAdd args destination ready called
          exact ⟨spec.2.2.2.2.1, spec.2.2.2.2.2.1, spec.2.2.2.2.2.2.1,
            Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel) valid hc hw ready bounded parts.1 (above.prepare_any code) called⟩
        | storageLive destination | storageDead destination | assign destination rhs | drop destination | fakeRead place | undefinedBehavior =>
          all_goals
            have raw := run
            simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at raw
            obtain ⟨⟨ending, endingActive⟩, acted, last⟩ := raw
            cases last
            have spec := Derived.action_spec valid hc hw _ acted
            exact ⟨spec.valid, spec.callers, spec.wellFormed,
              Derived.action_keeps_owner_provenance valid hc hw parts.1 (above.prepare_any code) acted⟩
      have count := (instruction_shape run).2.1
      exact ih tail next.1 next.2.1 next.2.2.1 (by rw [count]; exact bounded)
        (fun function args destination member => onlyScalar function args destination (List.mem_cons_of_mem act member)) parts.2 next.2.2.2

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
