module

public import SubtreeProofs.Rust.SourceQueryLoanOrigins

/-! Shared argument loans originate in the pre-entry readable packet, below
that world's memory length. Adding fresh parameter stack roots contributes
local reads, but does not add those stack roots to the shared-loan footprint. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem initial_shared_loan_origin {world : World} (hw : world.WellFormed) (frame count : Nat)
    {packets : List ValueCell} {slot : Nat} {cell : Cell} {value : Value}
    (positive : 0 < slot) (selected : packets[slot - 1]? = some (cell, .reference value))
    (readable : Readable world.memory world.live cell (.reference value)) :
    LoanOrigin (world.stackCells frame (packets.map Prod.fst)) (initialActivation world frame count packets)
      world.memory.length slot := by
  have indexBound : slot - 1 < packets.length := (List.getElem?_eq_some_iff.mp selected).choose
  have slotBound : slot ≤ packets.length := by omega
  let entered := world.stackCells frame (packets.map Prod.fst)
  let active := initialActivation world frame count packets
  let binding : Binding := ⟨world.memory.length + (slot - 1), world.memory.length + (slot - 1)⟩
  have root : active.roots slot = some binding := by
    simp only [active, initialActivation, argumentRoots, positive, slotBound, and_self, ite_true, binding]
  have memory : entered.memory[binding.address]? = some cell := by
    change (world.memory ++ packets.map Prod.fst)[world.memory.length + (slot - 1)]? = some cell
    rw [List.getElem?_append_right (by omega)]
    simp only [show world.memory.length + (slot - 1) - world.memory.length = slot - 1 by omega,
      List.getElem?_map, selected, Option.map_some]
  have classified : entered.classes binding.address = some (.stack active.frame slot binding.generation) := by
    simp only [entered, active, initialActivation, binding, World.stackCells,
      show ¬ world.memory.length + (slot - 1) < world.memory.length by omega, ite_false, List.length_map,
      show world.memory.length + (slot - 1) < world.memory.length + packets.length by omega, ite_true,
      show world.memory.length + (slot - 1) - world.memory.length + 1 = slot by omega]
  have state : active.state slot = .shared value := by
    simp only [active, initialActivation, SourceEval.initialState, Partial.Locals.lift, initialEnv,
      show slot ≠ 0 by omega, ite_false, List.getElem?_map, selected, Option.map_some, Slot.ofValue]
  obtain ⟨loans, graph, alive⟩ := readable
  have bound : ∀ address ∈ loans, address < world.memory.length := fun address member => hw.2 address (alive address member)
  have kept := world.stackCells_keeps hw frame (packets.map Prod.fst) (loans ++ [binding.address])
  cases graph with
  | @shared pointer target value reads selectedTarget child =>
    have graph : Graph entered.memory (.shared pointer) (.reference value) (reads ++ [pointer.root]) :=
      (Graph.shared selectedTarget child).mono kept.memory
    let resources : Resources := ⟨reads ++ [pointer.root], [], reads ++ [pointer.root]⟩
    have represented : ResourceRep entered.memory (.shared pointer) (active.state slot) resources := by
      rw [state]
      exact ⟨.shared graph, .shared graph.represents, .shared graph⟩
    refine ⟨resources.atRoot binding.address, .stored root memory classified represented ?_, bound⟩
    intro address member
    rcases List.mem_append.mp member with old | fresh
    · exact kept.alive address (List.mem_append_left _ old) (alive address old)
    · have same : address = binding.address := List.mem_singleton.mp fresh
      subst address
      simp only [binding, World.stackCells,
        show ¬ world.memory.length + (slot - 1) < world.memory.length by omega, ite_false, List.length_map,
        show world.memory.length + (slot - 1) < world.memory.length + packets.length by omega, decide_true]

end SubtreeProofs.Rust.SourceEval.Addressed
