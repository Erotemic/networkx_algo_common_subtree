module

public import SubtreeProofs.Rust.LookupHeapExecution
public import SubtreeProofs.Rust.LookupHeapTyping
public import SubtreeProofs.Rust.LookupHeapInputs
public import SubtreeProofs.Rust.LookupSourceCertificate

/-! Concrete addressed-memory realization of the checked lookup program.
This proves total successful execution at the established sufficient fuel,
typed first-hit readback, exact source currencies and actual fresh-cell growth.
The memory is immutable apart from allocation. Unique Box ownership, stack
borrows/destruction and official typed LLBC/Rust adequacy remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

theorem program_borrows (function : Function) : codeBorrows (Program.body function) = true := by
  cases function <;> decide +kernel

theorem mutant_borrows (function : Function) : codeBorrows (ExtraCompare.body function) = true := by
  cases function <;> decide +kernel

/-- Both concrete control certificates can use the independently implemented
heap primitives. This statement uses the original retained source program. -/
theorem certified_run_spec (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost)
    (hargs : RepresentsFields memory cells values)
    (hr : Control.run Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, run Program.body fuel function cells memory = some (cell, after, cost) ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  rw [Certificate.original_run] at hr
  exact run_spec Program.body program_borrows fuel function memory cells values value cost hargs hr

theorem certified_mutant_spec (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost)
    (hargs : RepresentsFields memory cells values)
    (hr : Control.run Certificate.mutant.body fuel function values = some (value, cost)) :
    ∃ cell after, run ExtraCompare.body fuel function cells memory = some (cell, after, cost) ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  rw [Certificate.mutant_run] at hr
  exact run_spec ExtraCompare.body mutant_borrows fuel function memory cells values value cost hargs hr

open verified_ordered_core in
theorem copy_spec (word : BalancedWord) (memory : Memory) (args : List Cell)
    (hargs : RepresentsFields memory args [.reference (encodeWord word)])
    (fuel : Nat) (hf : wordHeight word ≤ fuel) :
    ∃ cell after cost, run Program.body fuel .copyWord args memory = some (cell, after, cost) ∧
      Represents after cell (encodeWord word) ∧ Typed after cell (.adt .word) ∧
      Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.copy word).2 := by
  obtain ⟨cost, hr, hevents⟩ := copy_source word fuel hf
  obtain ⟨cell, after, hheap, hv, hext, hlen⟩ :=
    run_spec Program.body program_borrows fuel .copyWord memory args _ _ cost hargs hr
  exact ⟨cell, after, cost, hheap, hv, hv.typed (word_typed _), hext, hlen, hevents⟩

open verified_ordered_core in
theorem compare_spec (first second : BalancedWord) (memory : Memory) (args : List Cell)
    (hargs : RepresentsFields memory args [.reference (encodeWord first), .reference (encodeWord second)])
    (fuel : Nat) (hf : wordHeight first ≤ fuel) :
    ∃ cost, run Program.body fuel .compare args memory =
        some (.boolean (LookupEvents.compare first second).1, memory, cost) ∧
      cost.events = ⟨0, (LookupEvents.compare first second).2, 0, 0, 0⟩ := by
  obtain ⟨cost, hr, hevents⟩ := compare_source first second fuel hf
  obtain ⟨cell, after, hheap, hv, hext, hlen⟩ :=
    run_spec Program.body program_borrows fuel .compare memory args _ _ cost hargs hr
  have hm : after = memory := hext.eq_of_length (by simpa [hevents] using hlen)
  subst after
  cases hv
  exact ⟨cost, hheap, hevents⟩

open verified_ordered_core in
theorem lookup_spec (table : MemoTable) (left right : BalancedWord)
    (memory : Memory) (args : List Cell)
    (hargs : RepresentsFields memory args
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)])
    (fuel : Nat) (hf : lookupDepth table left right ≤ fuel) :
    ∃ cell after cost,
      run Program.body fuel .lookup args memory = some (cell, after, cost) ∧
      Represents after cell (encodeOption (MemoizedOrderedSolver.findResult table left right)) ∧
      Typed after cell (.adt .optional) ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧
      cost.steps ≤ 256 * cost.events.units := by
  obtain ⟨cost, hr, hevents⟩ := lookup_source table left right fuel hf
  have hbound := program_source_bound hr
  rw [LookupEvents.lookup_value] at hr
  obtain ⟨cell, after, hheap, hv, hext, hlen⟩ :=
    run_spec Program.body program_borrows fuel .lookup memory args _ _ cost hargs hr
  exact ⟨cell, after, cost, hheap, hv, hv.typed (option_typed _), hext, hlen, hevents, hbound⟩

open verified_ordered_core in
theorem lookup_all_runs (table : MemoTable) (left right : BalancedWord)
    (memory : Memory) (args : List Cell)
    (hargs : RepresentsFields memory args
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)])
    (fuel : Nat) (hf : lookupDepth table left right ≤ fuel) {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .lookup args memory = some (cell, after, cost)) :
    Represents after cell (encodeOption (MemoizedOrderedSolver.findResult table left right)) ∧
      Typed after cell (.adt .optional) ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧
      cost.steps ≤ 256 * cost.events.units := by
  obtain ⟨reference, mem, work, hs, hv, ht, hext, hlen, hevents, hb⟩ :=
    lookup_spec table left right memory args hargs fuel hf
  rw [hr] at hs
  cases hs
  exact ⟨hv, ht, hext, hlen, hevents, hb⟩

end SubtreeProofs.Rust.LookupSource.Heap
