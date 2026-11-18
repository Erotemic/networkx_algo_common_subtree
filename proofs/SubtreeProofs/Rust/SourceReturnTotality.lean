module

public import SubtreeProofs.Rust.SourceMovePermissions
public import SubtreeProofs.Rust.SourceOwnerControl

/-! Forward actual return extraction, with exact output ownership and source
cost. Materialization is an independent source-local fact. Actual root/loan
permissions construct the checked move; cleanup remains a separate step. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

def ReturnLoansAllowed (world : World) (active : Activation) (callers : List Activation) (binding : Binding) : Prop :=
  ∀ current suspended, Scanned world active current → Callers world callers suspended →
    binding.address ∉ current.loans ++ suspended.loans

theorem ReturnLoansAllowed.of_closed_preserved {before world : World} {active : Activation} {callers : List Activation}
    {binding : Binding} {previous : Resources}
    (typed : ∀ index < active.count, ∃ ty, SlotTyped (active.state index) ty ∧ Borrow.Closed ty)
    (callerView : Callers before callers previous) (hw : before.WellFormed)
    (kept : Preserves before world previous.reads) (fresh : before.memory.length ≤ binding.address) :
    ReturnLoansAllowed world active callers binding := by
  intro current suspended scanned currentCallers forbidden
  have empty := scanned.inventory.closed_loans (fun index hm => typed index (List.mem_range.mp hm))
  rw [empty, List.nil_append] at forbidden
  have bound := callerView.preserved_read_bound hw kept currentCallers binding.address
    (currentCallers.loans_subset_reads forbidden)
  omega

theorem returnValue_complete {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (separate : active.RootsSeparate callers)
    {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {binding : Binding} (hb : active.roots 0 = some binding) {value : Value}
    (ready : (active.state 0).materialize = some value) (loans : ReturnLoansAllowed world active callers binding) :
    ∃ cell, returnValue callers world active =
      some (.returned world {active with state := active.state.set 0 .empty} (cell, value), Cost.local 1) := by
  obtain ⟨current, hs, scanned⟩ := active.scan_complete ha
  obtain ⟨suspended, ht, callerView⟩ := scanCallers_complete callers hc
  have allowed := Addressed.allowed_local_from_loans ha separate hf callerView hb (loans current suspended scanned callerView)
  have source : SourceEval.operand active.state (.move (.local 0)) = some (value, active.state.set 0 .empty) := by
    simp only [SourceEval.operand, Partial.Locals.move, splitPlace, Slot.take, ready, bind, Option.bind]
  obtain ⟨cell, moved⟩ := Addressed.operand_complete scanned.frame source allowed
  exact ⟨cell, by simp only [returnValue, hs, ht, moved, bind, Option.bind]⟩

theorem returnValue_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {binding : Binding} (hb : active.roots 0 = some binding) {value : Value}
    (ready : (active.state 0).materialize = some value) (loans : ReturnLoansAllowed world active callers binding) :
    ∃ cell owners, returnValue callers world active =
        some (.returned world {active with state := active.state.set 0 .empty} (cell, value), Cost.local 1) ∧
      SourceEval.returnValue active.state = some (.returned value, Cost.local 1) ∧
      ({active with state := active.state.set 0 .empty} : Activation).Valid world ∧
      Readable world.memory world.live cell value ∧ Footprint world.memory cell owners ∧
      OwnerFrame world (owners ++ (({active with state := active.state.set 0 .empty} : Activation).owners world ++
        (callerOwners world callers ++ external))) ∧
      BoxCoverage world (owners ++ (({active with state := active.state.set 0 .empty} : Activation).owners world ++
        (callerOwners world callers ++ external))) := by
  obtain ⟨cell, run⟩ := returnValue_complete ha hc separate hf hb ready loans
  have checked := returnValue_spec ha hc hw run
  obtain ⟨owners, footprint, frame, coverage⟩ := returnValue_owner_resources ha hf covered run
  exact ⟨cell, owners, run, checked.1, checked.2.2.2.2.1.active, checked.2.2.2.2.1.packet,
    footprint, frame, coverage⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
