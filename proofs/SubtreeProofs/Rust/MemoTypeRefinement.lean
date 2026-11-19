module

public import SubtreeProofs.Rust.MemoTypeCalls
public import SubtreeProofs.Rust.MemoRegionCertificate
public import SubtreeProofs.Rust.MemoHeapRefinement
public import SubtreeProofs.Rust.LookupBorrowOutputs

/-! Checked source/static constraints imply operational typing for actual memo
runs, with full costs retained. Ordinary helper results contain no shared
reference even inside owned payloads. Dynamic loans/regions remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Types

open LookupSource LookupSource.Heap LookupSource.SourceTypes

theorem source_run_typed (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost) (types : List Ty) (ty : Ty)
    (hargs : RepresentsFields memory cells values) (ht : FieldsTyped memory cells types)
    (ho : callOutput function types = some ty)
    (hr : sourceRun Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      Typed after cell ty ∧ Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := MemoSource.Heap.certified_run_spec fuel function memory cells values value cost hargs hr
  have hp := original_run_typed fuel function cells types memory cell after cost ty ht ho hrun
  exact ⟨cell, after, hrun, hp.1, hv, hext, hlen⟩

theorem ordinary_output_closed (function : Function) (hf : function ≠ .boxNew) : Borrow.Closed (output function) := by
  cases function <;> first | contradiction | constructor

/-- This uses static-preservation typing, not the independent native result
specification. Generic Box is excluded because it may carry an existing loan. -/
theorem original_run_unborrowed (fuel : Nat) (function : Function) (hf : function ≠ .boxNew)
    (memory : Memory) (args : List Cell) (cell : Cell) (after : Memory) (cost : Cost)
    (hargs : FieldsTyped memory args (inputs function))
    (hr : MemoSource.Heap.run Program.body fuel function args memory = some (cell, after, cost)) :
    Typed after cell (output function) ∧ Extends memory after ∧ Borrow.Unborrowed after cell := by
  have ht : callOutput function (inputs function) = some (output function) := by
    simp only [callOutput, hf, ite_false, sameList_refl, ite_true]
  have hp := original_run_typed fuel function args (inputs function) memory cell after cost (output function) hargs ht hr
  exact ⟨hp.1, hp.2, Borrow.typed_unborrowed hp.1 (ordinary_output_closed function hf)⟩

theorem scoped_bodies_typed : ∃ program, Regions.read Input.Program.source = .ok program ∧ BodiesTyped Program.body := by
  obtain ⟨program, hr, hc⟩ := Regions.Certificate.original_program
  refine ⟨program, hr, ?_⟩
  intro function hf
  obtain ⟨decl, _, hfn, hcode⟩ := hc function hf
  have hb := decl.source.boundary
  have ht := decl.source.constraints
  have hdecl : decl.source.function = function := hfn
  rw [hdecl] at hb ht
  rw [hcode] at ht
  exact ⟨decl.source.locals, hb, ht⟩

/-- Operational typing consumes the declarations from the actual source read
that also carries all region-bearing annotations and their scope certificates. -/
theorem scoped_source_run_typed (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost) (types : List Ty) (ty : Ty)
    (hargs : RepresentsFields memory cells values) (ht : FieldsTyped memory cells types)
    (ho : callOutput function types = some ty)
    (hr : sourceRun Certificate.original.body fuel function values = some (value, cost)) :
    ∃ program, Regions.read Input.Program.source = .ok program ∧ ∃ cell after,
      MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      Typed after cell ty ∧ Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨program, hread, hb⟩ := scoped_bodies_typed
  obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := MemoSource.Heap.certified_run_spec fuel function memory cells values value cost hargs hr
  have hp := run_typed Program.body hb fuel function cells types memory cell after cost ty ht ho hrun
  exact ⟨program, hread, cell, after, hrun, hp.1, hv, hext, hlen⟩

end SubtreeProofs.Rust.MemoSource.Types
