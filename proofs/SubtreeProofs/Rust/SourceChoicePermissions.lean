module

public import SubtreeProofs.Rust.SourceLoanPermissions
public import SubtreeProofs.Rust.SourceEvalCallingCertificate
import all SubtreeProofs.Rust.SourceEvalCallingCertificate

/-! The actual pinned choice declaration has six closed local types. Independent
partial typing therefore discharges every remaining active shared-loan inventory,
including after moves. This is a forward permission fact, not whole-call success. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource Heap Partial Partial.Addressed Storage

theorem actual_local_types : CallingCertificate.originalChoice.locals =
    [.adt .embedding, .adt .embedding, .adt .embedding, .boolean, .u32, .u32] := by
  with_unfolding_all rfl

theorem actual_local_types_closed {ty : Ty} (h : ty ∈ CallingCertificate.originalChoice.locals) : Borrow.Closed ty := by
  rw [actual_local_types] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor

theorem typed_inventory_no_loans {world : World} {active : Activation} {slots : List Nat} {r : Resources}
    (typed : LocalsTyped CallingCertificate.originalChoice.locals active.state)
    (bound : active.count ≤ CallingCertificate.originalChoice.locals.length)
    (indices : ∀ slot ∈ slots, slot < active.count)
    (inventory : Inventory world active.frame active.roots active.state slots r) : r.loans = [] := by
  apply inventory.closed_loans
  intro slot hm
  have index : slot < CallingCertificate.originalChoice.locals.length := (indices slot hm).trans_le bound
  let ty := CallingCertificate.originalChoice.locals[slot]'index
  have lookup : CallingCertificate.originalChoice.locals[slot]? = some ty :=
    List.getElem?_eq_some_iff.mpr ⟨index, rfl⟩
  exact ⟨ty, typed slot ty lookup, actual_local_types_closed (List.getElem_mem index)⟩

end SubtreeProofs.Rust.SourceEval.Choice
