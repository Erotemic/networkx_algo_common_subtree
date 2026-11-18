module

public import SubtreeProofs.Rust.SourceEmbeddingLoanPermissions
public import SubtreeProofs.Rust.SourceOriginalLoanMachine

/-! A fresh table root can be moved beside both original bounded loans and
fresh native word/embedding views. Original referents need no new shape
restriction; only the fresh views use the native referent exclusion. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

def MemoLoanOrigins (limit : Nat) (world : World) (active : Activation) : Prop :=
  ∀ slot, LoanOrigin world active limit slot ∨ MemoLoans (active.state slot)

theorem OriginalLoanMachine.memo_origins {before world : World} {active : Activation}
    {callers : List Activation} {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) :
    MemoLoanOrigins before.memory.length world active := by
  intro slot
  by_cases member : slot ∈ exceptions
  · exact .inl (h.origins slot member)
  · obtain ⟨ty, typed, closed⟩ := h.closed slot member
    exact .inr (MemoLoans.of_closed typed closed)

theorem MemoLoanOrigins.prepare {limit : Nat} {world : World} {active : Activation}
    (h : MemoLoanOrigins limit world active) (code : Code) :
    MemoLoanOrigins limit world (active.forgetRefs code) := by
  intro slot
  rcases h slot with origin | data
  · exact .inl (origin.prepare code)
  · rcases LoanEnding.forget_eq_or_empty code (List.range active.count) active.state slot with same | empty
    · apply Or.inr
      change MemoLoans (LoanEnding.forget code _ active.state slot)
      rw [same]; exact data
    · apply Or.inr
      change MemoLoans (LoanEnding.forget code _ active.state slot)
      rw [empty]; exact .empty

theorem Inventory.memo_cells_above {limit : Nat} {world : World} {active : Activation}
    {slots : List Nat} {r : Resources}
    (inventory : Inventory world active.frame active.roots active.state slots r)
    (data : MemoLoanOrigins limit world active) :
    ∀ address ∈ r.loans, limit ≤ address → ∀ raw,
      world.memory[address]? = some raw → ¬ WordOpaque raw := by
  induction inventory with
  | nil => simp
  | @cons slot slots head tail first rest ih =>
    intro address member above raw read opaqueCell
    rcases List.mem_append.mp member with current | remaining
    · rcases data slot with origin | native
      · have below := origin.bound first address current
        omega
      · exact first.memo_cells native address current raw read opaqueCell
    · exact ih address remaining above raw read opaqueCell

theorem allowed_table_local_with_origins {before world : World} {active : Activation}
    {callers : List Activation} {previous current suspended : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (data : MemoLoanOrigins before.memory.length world active)
    (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {slot : Nat} {table : MemoTable} (initialized : active.state slot = Slot.ofValue (encodeTable table)) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move (.local slot)) := by
  intro cell pointer located forbidden
  obtain ⟨binding, root, same⟩ := locate_inline_root (place := .local slot) trivial located
  change active.roots slot = some binding at root
  have fresh := h.fresh slot binding root
  rw [same] at forbidden
  rcases List.mem_append.mp forbidden with localLoan | callerRead
  · obtain ⟨_, frame⟩ := h.valid.2
    obtain ⟨raw, used, read, _, graph, _⟩ := frame.get root
    have tableGraph : Graph world.memory raw (encodeTable table) used :=
      graph.materialize (by rw [initialized]; exact Slot.materialize_ofValue _)
    exact Inventory.memo_cells_above scanned.inventory data binding.address localLoan fresh raw read tableGraph.table_opaque
  · have old := h.previousCallers.preserved_read_bound h.beforeWellFormed h.kept callerView binding.address callerRead
    omega

end SubtreeProofs.Rust.SourceEval.Addressed
