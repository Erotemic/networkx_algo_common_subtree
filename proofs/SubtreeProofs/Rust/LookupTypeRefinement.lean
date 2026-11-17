module

public import SubtreeProofs.Rust.LookupTypeCalls
public import SubtreeProofs.Rust.LookupHeapRefinement

/-! Composition of checked source control, addressed realization and
operational type preservation, retaining the source execution's entire cost. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.SourceTypes

open Heap

theorem certified_run_typed (fuel : Nat) (function : Function) (cells : List Cell)
    (types : List Ty) (values : List Value) (memory : Memory) (value : Value) (cost : Cost) (ty : Ty)
    (hvalues : RepresentsFields memory cells values) (hargs : FieldsTyped memory cells types)
    (ht : callOutput function types = some ty)
    (hr : Control.run Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      Typed after cell ty ∧ Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, he, hv, hex, hlen⟩ :=
    Heap.certified_run_spec fuel function memory cells values value cost hvalues hr
  have hout := (original_run_typed fuel function cells types memory cell after cost ty hargs ht he).1
  exact ⟨cell, after, he, hout, hv, hex, hlen⟩

theorem certified_mutant_typed (fuel : Nat) (function : Function) (cells : List Cell)
    (types : List Ty) (values : List Value) (memory : Memory) (value : Value) (cost : Cost) (ty : Ty)
    (hvalues : RepresentsFields memory cells values) (hargs : FieldsTyped memory cells types)
    (ht : callOutput function types = some ty)
    (hr : Control.run Certificate.mutant.body fuel function values = some (value, cost)) :
    ∃ cell after, Heap.run ExtraCompare.body fuel function cells memory = some (cell, after, cost) ∧
      Typed after cell ty ∧ Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, he, hv, hex, hlen⟩ :=
    Heap.certified_mutant_spec fuel function memory cells values value cost hvalues hr
  have hout := (mutant_run_typed fuel function cells types memory cell after cost ty hargs ht he).1
  exact ⟨cell, after, he, hout, hv, hex, hlen⟩

end SubtreeProofs.Rust.LookupSource.SourceTypes
