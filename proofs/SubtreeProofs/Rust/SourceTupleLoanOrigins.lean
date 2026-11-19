module

public import SubtreeProofs.Rust.SourceQueryLoanOrigins

/-! A tuple assembled from two exact shared query pointers retains their loan
origins. The source tuple's own fresh stack root contributes reads, not loans;
repeated pointers and aliases between the query graphs remain permitted. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LoanOrigin.shared_graph {world : World} {active : Activation} {limit slot : Nat}
    (origin : LoanOrigin world active limit slot) {binding : Binding} {pointer : Pointer} {value : Value}
    (hb : active.roots slot = some binding) (raw : world.memory[binding.address]? = some (.shared pointer))
    (initialized : active.state slot = .shared value) :
    ∃ loans, Graph world.memory (.shared pointer) (.reference value) loans ∧ ∀ address ∈ loans, address < limit := by
  obtain ⟨r, represented, bound⟩ := origin
  cases represented with
  | vacant none _ => rw [hb] at none; cases none
  | @stored actual cell resources actualRoot memory classified payload alive =>
    have sameBinding := Option.some.inj (actualRoot.symm.trans hb)
    subst actual
    have sameCell := Option.some.inj (memory.symm.trans raw)
    subst cell
    have borrowed := payload.borrowed
    rw [initialized] at borrowed
    cases borrowed with
    | shared graph => exact ⟨_, graph, bound⟩

theorem LoanOrigin.tuple_shared {world : World} {active : Activation} {limit slot first second : Nat}
    (valid : active.Valid world) {tupleRoot firstRoot secondRoot : Binding} {leftPointer rightPointer : Pointer}
    {left right : Value} {kind : Kind} {tag : Nat}
    (tupleBinding : active.roots slot = some tupleRoot)
    (firstBinding : active.roots first = some firstRoot) (secondBinding : active.roots second = some secondRoot)
    (tupleRaw : world.memory[tupleRoot.address]? = some (.node kind tag [.shared leftPointer, .shared rightPointer]))
    (firstRaw : world.memory[firstRoot.address]? = some (.shared leftPointer))
    (secondRaw : world.memory[secondRoot.address]? = some (.shared rightPointer))
    (tupleValue : active.state slot = .node kind tag [.shared left, .shared right])
    (firstValue : active.state first = .shared left) (secondValue : active.state second = .shared right)
    (firstOrigin : LoanOrigin world active limit first) (secondOrigin : LoanOrigin world active limit second) :
    LoanOrigin world active limit slot := by
  obtain ⟨leftLoans, leftGraph, leftBound⟩ := firstOrigin.shared_graph firstBinding firstRaw firstValue
  obtain ⟨rightLoans, rightGraph, rightBound⟩ := secondOrigin.shared_graph secondBinding secondRaw secondValue
  obtain ⟨_, frame⟩ := valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot slot
  refine ⟨resources, represented, ?_⟩
  cases represented with
  | vacant none _ => rw [tupleBinding] at none; cases none
  | @stored actual cell parts actualRoot memory classified payload alive =>
    have sameBinding := Option.some.inj (actualRoot.symm.trans tupleBinding)
    subst actual
    have sameCell := Option.some.inj (memory.symm.trans tupleRaw)
    subst cell
    have borrowed := payload.borrowed
    rw [tupleValue] at borrowed
    change ∀ address ∈ parts.loans, address < limit
    generalize loanEq : parts.loans = loans at borrowed ⊢
    cases borrowed with
    | node fields => cases fields with
      | cons head rest => cases head with
        | shared firstGraph => cases rest with
          | cons tail last => cases tail with
            | shared secondGraph =>
              cases last
              rw [firstGraph.guards_unique leftGraph, secondGraph.guards_unique rightGraph]
              intro address member
              simp only [List.append_nil, List.mem_append] at member
              rcases member with leftMember | rightMember
              · exact leftBound address leftMember
              · exact rightBound address rightMember

end SubtreeProofs.Rust.SourceEval.Addressed
