module

public import SubtreeProofs.Rust.SourceClosedLoans
public import SubtreeProofs.Rust.SourceOwnerStorage

/-! Forward actual storage success. Fresh storage needs only declaration bounds
and an unbound slot. Retirement derives read separation from global owners,
separate roots and semantic shared-loan permissions, allowing initialized
nonowning locals. No successful source or addressed parent run is assumed. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

def RootLoansAllowed (world : World) (active : Activation) (callers : List Activation)
    (slot : Nat) (binding : Binding) : Prop :=
  ∀ remainder suspended,
    Inventory world active.frame active.roots active.state (remainingSlots active.count slot) remainder →
    Callers world callers suspended → binding.address ∉ remainder.loans ++ suspended.loans

theorem storageLive_complete {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) {slot : Nat}
    (bound : slot < active.count) (fresh : active.roots slot = none) :
    storageLive world active callers slot =
      some (world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 []),
        {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty}) := by
  obtain ⟨current, hs, _⟩ := active.scan_complete ha
  obtain ⟨suspended, ht, _⟩ := scanCallers_complete callers hc
  simp only [storageLive, bound, fresh, and_self, ite_true, hs, ht, bind, Option.bind]

theorem storageLive_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} (bound : slot < active.count) (fresh : active.roots slot = none) :
    ∃ final after, storageLive world active callers slot = some (final, after) ∧
      Step world active callers (.storageLive slot) final after (Cost.local 1) ∧ after.RootsSeparate callers ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  have run := storageLive_complete ha hc bound fresh
  have step := storageLive_spec ha hc hw run
  have owners := storageLive_owner_resources ha hc hw hf covered run
  exact ⟨_, _, run, step, separate.set_fresh hc slot _ (Nat.le_refl _), owners.2.2⟩

theorem storageDead_complete {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (zero : (active.state slot).dropWork.boxes = 0) (loans : RootLoansAllowed world active callers slot binding) :
    storageDead world active callers slot = some (world.retire [binding.address],
      {active with roots := active.roots.set slot none, state := active.state.set slot .empty}) := by
  obtain ⟨current, _, scanned⟩ := active.scan_complete ha
  obtain ⟨item, _, localRep⟩ := scanned.frame.inspectSlot slot
  obtain ⟨remainder, hr, remaining, _⟩ := active.context_complete ha slot
  obtain ⟨suspended, hs, callerView⟩ := scanCallers_complete callers hc
  have frame := Activation.partition_owner_frame ha hf hb localRep remaining callerView
  have remainingBoxes : BoxOwners world remainder.owners := fun a hm =>
    frame.classified a (List.mem_append_right _ (List.mem_append_left _ hm))
  have callerBoxes : BoxOwners world suspended.owners := fun a hm =>
    frame.classified a (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hm)))
  have allowed := loans remainder suspended remaining callerView
  have remainingLoan : binding.address ∉ remainder.loans := fun hm => allowed (List.mem_append_left _ hm)
  have callerLoan : binding.address ∉ suspended.loans := fun hm => allowed (List.mem_append_right _ hm)
  have remainingRoot := Activation.context_root_not_read ha hb remaining remainingBoxes remainingLoan
  have callerRoot := Activation.RootsSeparate.caller_root_not_read ha separate hb callerView callerBoxes callerLoan
  have noRead : binding.address ∉ remainder.reads ++ suspended.reads := by
    simpa only [List.mem_append, not_or] using And.intro remainingRoot callerRoot
  obtain ⟨_, _, _, classified, _, used⟩ := scanned.frame.get hb
  have live := scanned.frame.alive binding.address (used (List.mem_append_right _ (by simp)))
  have ended := world.endStack_success hw classified live noRead
  simp only [storageDead, zero, ite_true, scanContext, hr, hs, hb, ended, bind, Option.bind]

theorem storageDead_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (zero : (active.state slot).dropWork.boxes = 0) (loans : RootLoansAllowed world active callers slot binding) :
    ∃ final after, storageDead world active callers slot = some (final, after) ∧
      Step world active callers (.storageDead slot) final after (Cost.local 1) ∧ after.RootsSeparate callers ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  have run := storageDead_complete ha hc hw separate hf hb zero loans
  have step := (storageDead_spec ha hc hw run).1
  have owners := storageDead_owner_resources ha hc hw hf covered run
  exact ⟨_, _, run, step, separate.erase slot, owners.2.2⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
