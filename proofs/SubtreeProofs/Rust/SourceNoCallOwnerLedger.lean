module

public import SubtreeProofs.Rust.SourceOwnerControl
public import SubtreeProofs.Rust.SourceCallingNoCalls
public import SubtreeProofs.Rust.SourceClosedMachine

/-! Primitive control can move and destroy owners but cannot introduce new
owned identities. The actual return packet is included in this subset ledger. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

namespace Derived

theorem scrutinee_active_owner_perm {world : World} {active after : Activation} {callers : List Activation}
    {scrut : Scrutinee} {key : Key} (ha : active.Valid world)
    (run : scrutinee world active callers scrut = some (key, after)) :
    (active.owners world).Perm (after.owners world) := by
  simp only [scrutinee, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, _, suspended, _, ⟨actual, masks⟩, selected, last⟩ := run
  cases last
  exact Addressed.scrutinee_owners ha scrut selected

def Flow.OwnerSubset (owners : List Nat) : Flow → Prop
  | .next world active => active.owners world ⊆ owners
  | .returned world active packet => ∃ output, Footprint world.memory packet.1 output ∧ (output ++ active.owners world) ⊆ owners

theorem Flow.OwnerSubset.mono {first second : List Nat} {flow : Flow}
    (h : flow.OwnerSubset first) (subset : first ⊆ second) : flow.OwnerSubset second := by
  cases flow with
  | next world active => exact fun _ member => subset (h member)
  | returned world active packet =>
    obtain ⟨output, footprint, included⟩ := h
    exact ⟨output, footprint, fun _ member => subset (included member)⟩

end Derived

namespace Calling

open Derived

theorem exec_noCalls_owner_subset {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (owns : CallsOwn callee)
    {world : World} {active : Activation} {callers : List Activation} {external : List Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (code : Code) (noncall : noCalls code = true)
    (frame : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {flow : Flow} {cost : Cost} (run : exec callee callers code world active = some (flow, cost)) :
    flow.OwnerSubset (active.owners world) := by
  induction code generalizing world active flow cost with
  | done => cases run; exact fun _ member => member
  | ret =>
    obtain ⟨after, packet, output, rfl, footprint, _, partition⟩ := returnValue_owner_frame ha frame run
    exact ⟨output, footprint, partition.symm.subset⟩
  | step act rest ih =>
    have restNoncall : noCalls rest = true := by cases act <;> first | exact noncall | cases noncall
    have ready := readyFor_noCalls callee TypedReady callers (.step act rest) noncall world active
    rw [exec_step] at run
    cases acted : instruction callee callers (world, active.forgetRefs (.step act rest)) act with
    | none => simp [acted] at run
    | some pair =>
      rcases pair with ⟨⟨middle, current⟩, first⟩
      cases more : exec callee callers rest middle current with
      | none => simp [acted, more] at run
      | some pair =>
        rcases pair with ⟨result, last⟩
        simp only [acted, more, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        have observed := Activation.forgetRefs_valid ha (.step act rest)
        have beforeFrame : OwnerFrame world ((active.forgetRefs (.step act rest)).owners world ++ (callerOwners world callers ++ external)) := by
          simpa only [Activation.forgetRefs_owners] using frame
        have beforeCovered : BoxCoverage world ((active.forgetRefs (.step act rest)).owners world ++ (callerOwners world callers ++ external)) := by
          simpa only [Activation.forgetRefs_owners] using covered
        have raw : Derived.action world (active.forgetRefs (.step act rest)) callers act = some (middle, current) := by
          have h := acted
          cases act <;> try cases noncall
          all_goals
            simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at h
            obtain ⟨⟨w, a⟩, actual, last⟩ := h
            cases last
            exact actual
        have subset := action_owner_subset observed hc hw beforeFrame beforeCovered raw
        rw [Activation.forgetRefs_owners] at subset
        have step := instruction_spec respects observed hc hw act ready.1 acted
        have resources := instruction_owner_resources respects owns observed hc hw act ready.1 beforeFrame beforeCovered acted
        exact (ih step.valid step.callers step.wellFormed restNoncall resources.1 resources.2 more).mono subset
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    have parts := Bool.and_eq_true_iff.mp noncall
    have branches := Bool.and_eq_true_iff.mp parts.1
    have ready := readyFor_noCalls callee TypedReady callers (.switch scrut cases fallback left right rest) noncall world active
    rw [exec_switch] at run
    cases inspected : Derived.scrutinee world active callers scrut with
    | none => simp [inspected] at run
    | some pair =>
      rcases pair with ⟨key, current⟩
      have currentValid := (Derived.scrutinee_spec ha scrut inspected).2.2.2.2
      have resources := Derived.scrutinee_owner_resources ha scrut frame covered inspected
      have currentSubset := (scrutinee_active_owner_perm ha inspected).symm.subset
      obtain ⟨selected, resume⟩ := ready key current inspected
      cases selectedRun : Control.selectSource key cases fallback
          (fun _ => exec callee callers left world current) (fun _ => exec callee callers right world current) with
      | none => simp [inspected, selectedRun] at run
      | some pair =>
        rcases pair with ⟨branch, first⟩
        have subset : branch.OwnerSubset (current.owners world) := selected_spec key cases fallback selected
          (fun _ _ actual => ihLeft currentValid hc hw branches.1 resources.1 resources.2 actual)
          (fun _ _ actual => ihRight currentValid hc hw branches.2 resources.1 resources.2 actual) selectedRun
        have owned : branch.OwnerResources callers external := selected_spec key cases fallback selected
          (fun dom _ actual => exec_owner_resources respects owns currentValid hc hw left dom resources.1 resources.2 actual)
          (fun dom _ actual => exec_owner_resources respects owns currentValid hc hw right dom resources.1 resources.2 actual) selectedRun
        have valid : branch.Valid callers := selected_spec key cases fallback selected
          (fun dom _ actual => (exec_spec respects currentValid hc hw left dom actual).2.2.2)
          (fun dom _ actual => (exec_spec respects currentValid hc hw right dom actual).2.2.2) selectedRun
        simp only [inspected, selectedRun, bind, Option.bind] at run
        cases branch with
        | returned final after packet =>
          simp only [Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          exact subset.mono currentSubset
        | next middle after =>
          cases more : exec callee callers rest middle after with
          | none => simp [more] at run
          | some pair =>
            rcases pair with ⟨result, last⟩
            simp only [more, Option.some.injEq, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact (ihRest valid.active valid.callers valid.wellFormed parts.2 owned.1 owned.2 more).mono
              (fun _ member => currentSubset (subset member))

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
