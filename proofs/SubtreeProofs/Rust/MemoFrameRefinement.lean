module

public import SubtreeProofs.Rust.MemoFrameCalls
public import SubtreeProofs.Rust.MemoHeapRefinement

/-! Source composition of recursive memo local guards. These certificates
retain full execution/cost and prove cleanup independently of final ownership. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Frame

open LookupSource LookupSource.Heap LookupSource.Heap.Frame

theorem concatenate_profile (pl pr : Pointer) : ArgsMatch .concatenate [.shared pl, .shared pr] :=
  ⟨rfl, Or.inr ⟨Plain.shared pl, ⟨Plain.shared pr, trivial⟩⟩⟩

theorem insert_profile (table : Cell) (pl pr pc : Pointer) : ArgsMatch .insert [table, .shared pl, .shared pr, .shared pc] :=
  ⟨rfl, Or.inr ⟨by trivial, ⟨Plain.shared pl, ⟨Plain.shared pr, ⟨Plain.shared pc, trivial⟩⟩⟩⟩⟩

theorem source_run_guarded (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost)
    (hrep : RepresentsFields memory cells values) (hargs : ArgsMatch function cells)
    (hr : sourceRun Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunSafe Program.body fuel function cells memory cell after cost ∧
      Represents after cell value ∧ Extends memory after ∧ after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := MemoSource.Heap.certified_run_spec fuel function memory cells values value cost hrep hr
  exact ⟨cell, after, hrun, original_run_safe fuel function cells memory hargs hrun, hv, hext, hlen⟩

theorem concatenate_guarded (fuel : Nat) (memory : Memory) (pl pr : Pointer) {cell : Cell} {after : Memory} {cost : Cost}
    (hr : MemoSource.Heap.run Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost)) :
    RunSafe Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost :=
  original_run_safe fuel .concatenate _ memory (concatenate_profile pl pr) hr

theorem insert_guarded (fuel : Nat) (memory : Memory) (table : Cell) (pl pr pc : Pointer)
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : MemoSource.Heap.run Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost)) :
    RunSafe Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory cell after cost :=
  original_run_safe fuel .insert _ memory (insert_profile table pl pr pc) hr

end SubtreeProofs.Rust.MemoSource.Frame
