module

public import SubtreeProofs.Rust.SourceDropTotality
public import SubtreeProofs.Rust.SourcePartialTyping
public import SubtreeProofs.Rust.LookupBorrowOutputs
public import SubtreeProofs.Rust.SourceHeapOutputReadback

/-! Independently typed partial locals of closed types contain no shared loans,
including holes and partially moved owned Box shells. This discharges actual
loan inventories from type facts rather than from a successful physical run. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

mutual
  theorem BorrowFootprint.closed_loans {memory : Memory} {cell : Cell} {part : Slot} {ty : Ty} {loans : List Nat}
      (h : BorrowFootprint memory cell part loans) (ht : SlotTyped part ty) (closed : Borrow.Closed ty) : loans = [] := by
    cases ht with
    | empty _ => cases h; rfl
    | boolean _ => cases h; rfl
    | number _ => cases h; rfl
    | shared _ => cases closed
    | node shape fields => cases h with
      | node data => exact data.closed_loans fields (Borrow.shape_closed shape closed)
    | owned typed => cases closed with
      | owned inner => cases h with
        | owned _ child => exact child.closed_loans typed inner
  termination_by sizeOf part

  theorem BorrowFields.closed_loans {memory : Memory} {cells : List Cell} {parts : List Slot} {types : List Ty} {loans : List Nat}
      (h : BorrowFields memory cells parts loans) (ht : FieldsSlotTyped parts types) (closed : Borrow.ClosedFields types) : loans = [] := by
    cases ht with
    | nil => cases h; rfl
    | cons first rest => cases closed with
      | cons cf cr => cases h with
        | cons data tail => rw [data.closed_loans first cf, tail.closed_loans rest cr]; rfl
  termination_by sizeOf parts
end

theorem Graph.closed_reads {memory : Memory} {cell : Cell} {value : Value} {reads owners : List Nat} {ty : Ty}
    (h : Graph memory cell value reads) (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    (footprint : Footprint memory cell owners) : reads = owners := by
  have unborrowed := Borrow.typed_unborrowed (h.represents.typed typed) closed
  exact Rep.unique (Rep.of_full h.represents (h.footprint unborrowed)) (Rep.of_full h.represents footprint)

namespace Storage

theorem LocalResources.closed_loans {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) {ty : Ty}
    (typed : SlotTyped (state slot) ty) (closed : Borrow.Closed ty) : r.loans = [] := by
  cases h with
  | vacant _ _ => rfl
  | stored _ _ _ resources _ => exact resources.borrowed.closed_loans typed closed

theorem Inventory.closed_loans {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (h : Inventory world frame roots state slots r)
    (typed : ∀ slot ∈ slots, ∃ ty, SlotTyped (state slot) ty ∧ Borrow.Closed ty) : r.loans = [] := by
  induction h with
  | nil => rfl
  | @cons slot slots head tail first rest ih =>
    obtain ⟨ty, ht, closed⟩ := typed slot (by simp)
    have head := first.closed_loans ht closed
    have tail := ih (fun slot hm => typed slot (List.mem_cons_of_mem _ hm))
    simp only [Resources.plus, head, tail, List.nil_append]

theorem Callers.closed_loans {world : World} {callers : List Activation} {r : Resources}
    (h : Callers world callers r)
    (typed : ∀ active ∈ callers, ∀ slot < active.count, ∃ ty, SlotTyped (active.state slot) ty ∧ Borrow.Closed ty) :
    r.loans = [] := by
  induction h with
  | nil => rfl
  | @cons active callers head tail first rest ih =>
    have head := first.inventory.closed_loans (by
      intro slot hm
      exact typed active (by simp) slot (List.mem_range.mp hm))
    have tail := ih (fun active hm => typed active (List.mem_cons_of_mem _ hm))
    simp only [Resources.plus, head, tail, List.nil_append]

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
