module

public import SubtreeProofs.Rust.SourceMaximumEntryCertificate
public import SubtreeProofs.Rust.SourceNativeQueryEntry
public import SubtreeProofs.Rust.SourceOwnerEntry
public import SubtreeProofs.Rust.SourceOriginalLoanMachine

/-! Construct the actual seven-local public entry from two readable shared
queries and a complete retained owner frame. Query aliases are unrestricted;
their shared loan footprints stay below the original heap length. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Maximum

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def inputPackets (leftCell rightCell : Cell) (left right : BalancedWord) : List ValueCell :=
  [(leftCell, .reference (encodeWord left)), (rightCell, .reference (encodeWord right))]

theorem native_entry_machine {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (leftCell rightCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    {external : List Nat} (frame : OwnerFrame world (callerOwners world callers ++ external))
    (covered : BoxCoverage world (callerOwners world callers ++ external)) :
    ∃ entered active,
      enter world world.memory.length CallingCertificate.originalMaximum.source.localCount
        (inputPackets leftCell rightCell left right) = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [1, 2] entered active ∧
      active.state = initialState [.reference (encodeWord left), .reference (encodeWord right)] ∧
      active.count = 7 ∧ (∀ slot, slot ∉ [1, 2] → active.roots slot = none) := by
  let packets := inputPackets leftCell rightCell left right
  let entered := world.stackCells world.memory.length (packets.map Prod.fst)
  let active := initialActivation world world.memory.length 7 packets
  have readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
    intro p member
    simp only [packets, inputPackets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftRead
    · exact rightRead
  have footprint : FieldsFootprint world.memory [leftCell, rightCell] [] := by
    obtain ⟨_, first, _⟩ := leftRead
    obtain ⟨_, second, _⟩ := rightRead
    cases first with | shared _ _ => cases second with | shared _ _ => exact .cons (.shared _) (.cons (.shared _) .nil)
  obtain ⟨entryRun, valid, wf, keep⟩ := enter_complete hw world.memory.length 7 readable (by simp [packets, inputPackets])
  change active.Valid entered at valid
  have own := enter_owner_resources hw world.memory.length 7 hc readable footprint
    (by simpa using frame) (by simpa using covered) entryRun
  have safe : LoanSafeState active.state := by
    apply LoanSafeState.initial
    intro value member
    simp only [packets, inputPackets, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.word left)
    · simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.word right)
  have native : LoanSafeMachine world callers previous external entered active := by
    refine ⟨hw, view, (keep previous.reads).preserves, valid, wf,
      initialActivation_rootsSeparate hc _ _ _, ?_, ?_, safe, own.1, own.2⟩
    · simp only [entered, World.stackCells, List.length_append]; omega
    · intro slot binding hb
      simp only [active, initialActivation, argumentRoots] at hb
      split at hb
      next => cases hb; change world.memory.length ≤ world.memory.length + (slot - 1); omega
      next => cases hb
  have unbound : ∀ slot, slot ∉ [1, 2] → active.roots slot = none := by
    intro slot outside
    have one : slot ≠ 1 := by intro same; subst slot; simp at outside
    have two : slot ≠ 2 := by intro same; subst slot; simp at outside
    simp only [active, initialActivation, argumentRoots, packets, inputPackets,
      List.length_cons, List.length_nil, Nat.reduceAdd]
    have no : ¬ (0 < slot ∧ slot ≤ 2) := by omega
    simp only [no, ite_false]
  have original : OriginalLoanMachine world callers previous external [1, 2] entered active := by
    refine ⟨native, ?_, ?_, ?_⟩
    · intro slot outside
      obtain ⟨_, actual⟩ := valid.2
      have empty : active.state slot = .empty := by simpa only [unbound slot outside] using actual.slots slot
      exact ⟨.u32, empty ▸ SlotTyped.empty .u32, .u32⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [active, initialActivation, packets, inputPackets, initialState,
          Partial.Locals.lift, initialEnv, Slot.ofValue, Slot.dropWork]
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact initial_shared_loan_origin hw world.memory.length 7 (by decide) (by rfl) leftRead
      · exact initial_shared_loan_origin hw world.memory.length 7 (by decide) (by rfl) rightRead
  refine ⟨entered, active, ?_, original, rfl, rfl, unbound⟩
  rw [CallingCertificate.originalMaximum_spec.2.1]
  exact entryRun

end SubtreeProofs.Rust.SourceEval.Maximum
