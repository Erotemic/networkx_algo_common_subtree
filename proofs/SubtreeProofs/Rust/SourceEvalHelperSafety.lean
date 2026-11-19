module

public import SubtreeProofs.Rust.SourceEvalHelperRefinement
public import SubtreeProofs.Rust.MemoRegionRefinement
public import SubtreeProofs.Rust.LookupRegionRefinement

/-! Composition with the completed addressed helper proofs. The new source
runs and old addressed/typing/owner/storage/loan/region witnesses share exactly
one old work cost, embedded with zero added destruction and solver calls.
This transfers helper results; it is not addressed safety for the evaluator. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Helpers

open LookupSource LookupSource.Heap LookupSource.Heap.Borrow Legacy verified_ordered_core

theorem lookup_source_scoped (base : Memory) (fuel : Nat) (function : LookupSource.Function)
    (cells : List Cell) (types : List Heap.Ty) (values : List LookupSource.Value) (memory : Memory)
    (value : LookupSource.Value) (cost : LookupSource.Cost) (ty : Heap.Ty)
    (hb : FieldsBounded values) (hext : Extends base memory) (hv : RepresentsFields memory cells values)
    (ha : FieldsSafe base memory cells types) (ht : SourceTypes.callOutput function types = some ty)
    (hr : Control.run LookupSource.Certificate.original.body fuel function values = some (value, cost)) :
    SourceEval.run Certificate.original.body fuel (lookupFunction function) values = some (value, costMap cost) ∧
    ∃ program, Regions.Reader.read LookupSource.Input.Program.source = .ok program ∧ ∃ cell after,
      Heap.run LookupSource.Program.body fuel function cells memory = some (cell, after, cost) ∧
      Regions.RunScoped base program LookupSource.Program.body fuel function cells memory cell after cost ∧
      Safe base after cell ty ∧ Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations :=
  ⟨(lookup_run fuel function values value cost hb hr).2,
    Regions.source_run_scoped base fuel function cells types values memory value cost ty hext hv ha ht hr⟩

theorem memo_source_scoped (base : Memory) (fuel : Nat) (function : MemoSource.Function) (memory : Memory)
    (cells : List Cell) (types : List Heap.Ty) (values : List LookupSource.Value)
    (value : LookupSource.Value) (cost : LookupSource.Cost) (ty : Heap.Ty)
    (hb : FieldsBounded values) (hext : Extends base memory) (hv : RepresentsFields memory cells values)
    (ha : FieldsSafe base memory cells types) (ht : MemoSource.Types.callOutput function types = some ty)
    (hr : MemoSource.sourceRun MemoSource.Certificate.original.body fuel function values = some (value, cost)) :
    SourceEval.run Certificate.original.body fuel (memoFunction function) values = some (value, costMap cost) ∧
    ∃ program, MemoSource.Regions.read MemoSource.Input.Program.source = .ok program ∧ ∃ cell after,
      MemoSource.Heap.run MemoSource.Program.body fuel function cells memory = some (cell, after, cost) ∧
      MemoSource.Regions.RunScoped base program MemoSource.Program.body fuel function cells memory cell after cost ∧
      Safe base after cell ty ∧ Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations :=
  ⟨(memo_run fuel function values value cost hb hr).2,
    MemoSource.Regions.source_run_scoped base fuel function memory cells types values value cost ty hext hv ha ht hr⟩

theorem concatenate_source_total (left right : BalancedWord) (fuel : Nat)
    (hf : MemoSource.concatenateDepth left right ≤ fuel) (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ program, MemoSource.Regions.read MemoSource.Input.Program.source = .ok program ∧ ∃ cell after cost,
      SourceEval.run Certificate.original.body fuel .concatenate
        [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), costMap cost) ∧
      MemoSource.Heap.run MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost) ∧
      MemoSource.Regions.RunScoped memory program MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      MemoSource.Borrow.RunSafe memory MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Safe memory after cell (.adt .word) ∧ Unborrowed after cell ∧
      MemoSource.Stack.RunSafe MemoSource.Stack.Certificate.original MemoSource.Stack.Certificate.originalCount fuel
        .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      MemoSource.Spatial.RunSpatial MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      MemoSource.Frame.RunSafe MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Represents after cell (encodeWord (OrderedSolver.appendWord left right)) ∧ Typed after cell (.adt .word) ∧
      Owns after cell memory.length after.length ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧ cost.events = MemoSource.concatenateEvents left right ∧
      verified_ordered_core.concatenate left right = .ok (OrderedSolver.appendWord left right) ∧
      (∀ frame, Spatial.Separated memory frame → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Loan memory pointer ty → ∃ target, Heap.read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨program, hread, cell, after, cost, hr, rest⟩ :=
    MemoSource.Regions.concatenate_source_total left right fuel hf memory pl pr hLeft hRight
  exact ⟨program, hread, cell, after, cost,
    (memo_run fuel .concatenate _ _ cost
      (.cons (.reference (word_bounded left)) (.cons (.reference (word_bounded right)) .nil)) hr).2, rest⟩

theorem insert_source_total (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : MemoSource.insertDepth left right result ≤ fuel) (memory : Memory) (tc : Cell) (pl pr pc : Pointer)
    (hTable : Represents memory tc (encodeTable table))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result))) :
    ∃ program, MemoSource.Regions.read MemoSource.Input.Program.source = .ok program ∧ ∃ cell after cost,
      SourceEval.run Certificate.original.body fuel .insert
        [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), costMap cost) ∧
      MemoSource.Heap.run MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost) ∧
      MemoSource.Regions.RunScoped memory program MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      MemoSource.Borrow.RunSafe memory MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Safe memory after cell (.adt .table) ∧ Unborrowed after cell ∧
      MemoSource.Stack.RunSafe MemoSource.Stack.Certificate.original MemoSource.Stack.Certificate.originalCount fuel
        .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      MemoSource.Spatial.RunSpatial MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      MemoSource.Frame.RunSafe MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Represents after cell (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧ Typed after cell (.adt .table) ∧
      Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      cost.events = MemoSource.insertEvents left right result ∧
      verified_ordered_core.memo_insert table left right result = .ok (.Entry ⟨left, right, result⟩ table) ∧
      (∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ after[tail]? = some tc ∧ memory.length ≤ tail) ∧
      (∀ frame, Spatial.Separated memory (tc :: frame) → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Loan memory pointer ty → ∃ target, Heap.read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨program, hread, cell, after, cost, hr, rest⟩ :=
    MemoSource.Regions.insert_source_total table left right result fuel hf memory tc pl pr pc hTable hLeft hRight hResult
  exact ⟨program, hread, cell, after, cost,
    (memo_run fuel .insert _ _ cost (.cons (table_bounded table)
      (.cons (.reference (word_bounded left)) (.cons (.reference (word_bounded right))
        (.cons (.reference (result_bounded result)) .nil)))) hr).2, rest⟩

end SubtreeProofs.Rust.SourceEval.Helpers
