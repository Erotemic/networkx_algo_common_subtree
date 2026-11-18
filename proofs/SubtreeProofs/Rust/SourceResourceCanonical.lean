module

public import SubtreeProofs.Rust.SourceReadPartition

/-! Represented resource inventories are the exact actual tracer/scan outputs.
Thus complete shared-loan lists as well as owner lists are canonical, and a
preserved caller inventory can discharge permissions at a later symbolic world. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

mutual
  theorem ResourceRep.trace {memory : Memory} {cell : Cell} {part : Slot} {r : Resources}
      (h : ResourceRep memory cell part r) : traceResources memory cell part = some r := by
    rcases h with ⟨graph, owned, borrowed⟩
    rcases r with ⟨reads, owners, loans⟩
    cases borrowed with
    | empty _ => cases graph; cases owned; simp only [traceResources]
    | boolean _ => cases graph; cases owned; simp [traceResources]
    | number _ => cases graph; cases owned; simp [traceResources]
    | node fields => cases graph with | node data => cases owned with
      | node owners => simpa only [traceResources, and_self, ite_true] using FieldsResourceRep.trace ⟨data, owners, fields⟩
    | shared loan => cases graph with | shared data => cases owned with
      | shared _ =>
        have same := loan.guards_unique data
        simp only [traceResources, data.trace, bind, Option.bind]
        cases same
        rfl
    | owned hr child => cases graph with | owned hs data => cases owned with
      | owned ht owners =>
        cases Option.some.inj (hr.symm.trans hs)
        cases Option.some.inj (hr.symm.trans ht)
        rename_i address cell part childReads childOwners
        have traced := ResourceRep.trace (r := ⟨childReads, childOwners, loans⟩) ⟨data, owners, child⟩
        simp only [traceResources, hr, traced, bind, Option.bind]
        rfl
  termination_by sizeOf part

  theorem FieldsResourceRep.trace {memory : Memory} {cells : List Cell} {parts : List Slot} {r : Resources}
      (h : FieldsResourceRep memory cells parts r) : traceFieldsResources memory cells parts = some r := by
    rcases h with ⟨graph, owned, borrowed⟩
    rcases r with ⟨reads, owners, loans⟩
    cases borrowed with
    | nil => cases graph; cases owned; simp only [traceFieldsResources]
    | cons first rest => cases graph with | cons data tail => cases owned with
      | cons owned more =>
        rename_i cell part cells parts firstLoans restLoans firstReads restReads firstOwners restOwners
        have head := ResourceRep.trace (r := ⟨firstReads, firstOwners, firstLoans⟩) ⟨data, owned, first⟩
        have last := FieldsResourceRep.trace (r := ⟨restReads, restOwners, restLoans⟩) ⟨tail, more, rest⟩
        simp only [traceFieldsResources, head, last, Resources.plus, bind, Option.bind]
        rfl
  termination_by sizeOf parts
end

namespace Storage

theorem LocalResources.inspect {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) : inspectSlot world frame roots state slot = some r := by
  cases h with
  | vacant root empty => simp only [inspectSlot, root, empty, SourceEval.Addressed.emptySlot, ite_true]
  | stored root cell classified resources alive =>
    simp only [inspectSlot, root, classified, ite_true, cell, resources.trace, bind, Option.bind,
      List.all_eq_true.mpr alive]

theorem Inventory.inspect {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (h : Inventory world frame roots state slots r) :
    inspect world frame roots state slots = some r := by
  induction h with
  | nil => rfl
  | cons first rest ih => simp only [Storage.inspect, first.inspect, ih, bind, Option.bind]

theorem Scanned.scan {world : World} {active : Activation} {r : Resources} (h : Scanned world active r) :
    active.scan world = some r := h.inventory.inspect

theorem Callers.scan {world : World} {callers : List Activation} {r : Resources} (h : Callers world callers r) :
    scanCallers world callers = some r := by
  induction h with
  | nil => rfl
  | cons first rest ih => simp only [scanCallers, first.scan, ih, bind, Option.bind]

theorem Callers.unique {world : World} {callers : List Activation} {first second : Resources}
    (h : Callers world callers first) (h' : Callers world callers second) : first = second :=
  Option.some.inj (h.scan.symm.trans h'.scan)

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
