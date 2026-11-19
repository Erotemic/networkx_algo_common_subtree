module

public import SubtreeProofs.Rust.SourceMovedOwnerProvenance

/-! Actual expression packets retain source owner bounds. Aggregates combine
only the owned occurrences of their actual operands; guarded assignment then
preserves that packet provenance in its selected destination. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def OperandSourcesAbove (bound : Nat) (world : World) (active : Activation) (ops : List Operand) : Prop :=
  ∀ op ∈ ops, ∀ place, op = .move place → LocalOwnersAbove bound world active (splitPlace place).1

theorem operands_owner_provenance {bound : Nat} {world : World} {active : Activation} {guarded : List Nat}
    (ops : List Operand) {packets : List ValueCell} {masks : State}
    (ha : active.Valid world) (run : operands world active.roots guarded active.state ops = some (packets, masks)) :
    (∀ slot, LocalOwnersAbove bound world active slot → LocalOwnersAbove bound world {active with state := masks} slot) ∧
    (OperandSourcesAbove bound world active ops → ∀ packet ∈ packets, CellOwnersAbove bound world.memory packet.1) := by
  induction ops generalizing active packets masks with
  | nil => cases run; exact ⟨fun _ above => above, by simp⟩
  | cons op rest ih =>
    simp only [operands, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨packet, middle⟩, firstRun, ⟨tail, ending⟩, tailRun, run⟩ := run
    cases run
    obtain ⟨boundedRoots, guards, frame⟩ := ha
    obtain ⟨_, _, _, _, middleFrame⟩ := operand_spec frame firstRun
    have middleValid : ({active with state := middle} : Activation).Valid world := ⟨boundedRoots, guards, middleFrame⟩
    obtain ⟨firstKept, firstFresh⟩ := operand_owner_provenance (bound := bound) ⟨boundedRoots, guards, frame⟩ firstRun
    obtain ⟨tailKept, tailFresh⟩ := ih middleValid tailRun
    refine ⟨fun slot above => tailKept slot (firstKept slot above), ?_⟩
    intro selected actual member
    rcases List.mem_cons.mp member with rfl | old
    · exact firstFresh (fun place same => selected op (by simp) place same)
    · apply tailFresh ?_ actual old
      intro selectedOp selectedMember place same
      exact firstKept _ (selected selectedOp (List.mem_cons_of_mem op selectedMember) place same)

theorem fields_owner_provenance {bound : Nat} {memory : Memory} {cells : List Cell}
    (above : ∀ cell ∈ cells, CellOwnersAbove bound memory cell) {owners : List Nat}
    (footprint : FieldsFootprint memory cells owners) : ∀ address ∈ owners, bound ≤ address := by
  induction cells generalizing owners with
  | nil => cases footprint; simp
  | cons cell cells ih =>
    obtain ⟨first, rest, rfl, head, tail⟩ := footprint.cons_inv
    intro address member
    rcases List.mem_append.mp member with one | more
    · exact above cell (by simp) first head address one
    · exact ih (fun selected member => above selected (List.mem_cons_of_mem cell member)) tail address more

def ExpressionSourcesAbove (bound : Nat) (world : World) (active : Activation) (rhs : Expr) : Prop :=
  match rhs with
  | .use op => OperandSourcesAbove bound world active [op]
  | .aggregate _ _ ops => OperandSourcesAbove bound world active ops
  | .address _ | .less _ _ => True

theorem expression_owner_provenance {bound : Nat} {world : World} {active : Activation} {guarded : List Nat}
    {rhs : Expr} {packet : ValueCell} {masks : State} (ha : active.Valid world)
    (selected : ExpressionSourcesAbove bound world active rhs)
    (run : expression world active.roots guarded active.state rhs = some (packet, masks)) :
    CellOwnersAbove bound world.memory packet.1 := by
  cases rhs with
  | use op => exact (operand_owner_provenance ha run).2 (fun place same => selected op (by simp) place same)
  | aggregate kind tag ops =>
    simp only [expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨packets, masks⟩, arguments, run⟩ := run
    cases run
    have above := (operands_owner_provenance ops ha arguments).2 selected
    intro owners footprint
    exact fields_owner_provenance (by
      intro cell member
      obtain ⟨packet, packetMember, rfl⟩ := List.mem_map.mp member
      exact above packet packetMember) footprint.node_inv
  | address place =>
    obtain ⟨_, guards, frame⟩ := ha
    cases read : active.state.read place with
    | none => simp [expression, read] at run
    | some value =>
      obtain ⟨pointer, used, borrow, _, _⟩ := frame.borrow place read
      simp only [expression, read, borrow, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact CellOwnersAbove.of_footprint (.shared pointer) (by simp)
  | less first second =>
    simp only [expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨⟨leftCell, leftValue⟩, middle⟩, _, ⟨⟨rightCell, rightValue⟩, ending⟩, _, run⟩ := run
    cases leftCell <;> cases rightCell <;> try cases run
    simp only [Option.bind_eq_some_iff] at run
    obtain ⟨answer, _, run⟩ := run
    cases run
    exact CellOwnersAbove.of_footprint (.boolean answer) (by simp)

namespace Derived

theorem assign_owner_provenance {bound : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {slot : Nat} {rhs : Expr} (ha : active.Valid world)
    (selected : ExpressionSourcesAbove bound world active rhs)
    (run : assign world active callers slot rhs = some (final, after)) : LocalOwnersAbove bound final after slot := by
  simp only [assign, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, currentScan, suspended, callerScan, ⟨packet, masks⟩, expressionRun,
    remainder, remainderScan, ⟨next, state⟩, stored, last⟩ := run
  cases last
  have frame := (Activation.scan_spec ha currentScan).frame
  have above := expression_owner_provenance ha selected expressionRun
  obtain ⟨owners, footprint, _⟩ := expression_owners ha expressionRun
  have packetRead := (expression_readable frame expressionRun).2.1
  have exactOwners := store_local_owners packetRead footprint stored
  intro resources represented address member
  rw [exactOwners resources represented] at member
  exact above owners footprint address member

end Derived
end SubtreeProofs.Rust.SourceEval.Addressed
