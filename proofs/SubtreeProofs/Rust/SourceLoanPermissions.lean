module

public import SubtreeProofs.Rust.SourceCloseTotality
public import SubtreeProofs.Rust.SourceResourceCanonical

/-! Derive current loan permissions from independent closed local types and
preserved actual caller inventories. Old caller reads stay below the original
memory boundary; fresh local roots need no unique symbolic frame identifier.
No successful parent execution is used to assert the required separation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem Callers.preserved_read_bound {before world : World} {callers : List Activation} {previous : Resources}
    (h : Callers before callers previous) (hw : before.WellFormed) (kept : Preserves before world previous.reads)
    {current : Resources} (now : Callers world callers current) :
    ∀ address ∈ current.reads, address < before.memory.length := by
  have same := now.unique (h.transport kept)
  rw [same]
  exact fun address hm => hw.2 address (h.alive address hm)

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem RootLoansAllowed.of_closed_preserved {before world : World} {active : Activation} {callers : List Activation}
    {slot : Nat} {binding : Binding} {previous : Resources}
    (typed : ∀ index ∈ remainingSlots active.count slot, ∃ ty, SlotTyped (active.state index) ty ∧ Borrow.Closed ty)
    (callerView : Callers before callers previous) (hw : before.WellFormed)
    (kept : Preserves before world previous.reads) (fresh : before.memory.length ≤ binding.address) :
    RootLoansAllowed world active callers slot binding := by
  intro remainder suspended remaining current forbidden
  have empty := remaining.closed_loans typed
  rw [empty, List.nil_append] at forbidden
  have bound := callerView.preserved_read_bound hw kept current binding.address
    (current.loans_subset_reads forbidden)
  omega

theorem DropLoansAllowed.of_closed_preserved {before world : World} {active : Activation} {callers : List Activation}
    {slot : Nat} {binding : Binding} {previous : Resources}
    (typed : ∀ index ∈ remainingSlots active.count slot, ∃ ty, SlotTyped (active.state index) ty ∧ Borrow.Closed ty)
    (callerView : Callers before callers previous) (hw : before.WellFormed)
    (kept : Preserves before world previous.reads) (fresh : before.memory.length ≤ binding.address)
    (owned : ∀ item, LocalResources world active.frame active.roots active.state slot item →
      List.Disjoint item.owners previous.loans) : DropLoansAllowed world active callers slot binding := by
  intro item remainder suspended localRep remaining current
  have empty := remaining.closed_loans typed
  have same := current.unique (callerView.transport kept)
  rw [empty, List.nil_append, same]
  apply List.disjoint_left.mpr
  intro address member borrowed
  rcases List.mem_cons.mp member with root | owner
  · subst address
    have bound := callerView.preserved_read_bound hw kept (callerView.transport kept) binding.address
      (callerView.loans_subset_reads borrowed)
    omega
  · exact List.disjoint_left.mp (owned item localRep) owner borrowed

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
