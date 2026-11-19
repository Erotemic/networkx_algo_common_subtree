module

public import SubtreeProofs.Rust.SourceEvalHelperCertificate
public import SubtreeProofs.Rust.MemoSourceRefinement

/-! Recursive execution and native helper contracts reused in the actual
expanded evaluator program. All old instruction/event costs survive exactly;
this helper fragment destroys no remaining owned values and calls no solver. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Helpers

open LookupSource Legacy verified_ordered_core

def lookupDriver : Driver LookupSource.Function where
  body := LookupSource.Certificate.original.body
  box := .boxNew
  entry := LookupSource.entryEvents
  run := Control.run LookupSource.Certificate.original.body
  zero := by intros; rfl
  succ := Control.run_succ LookupSource.Certificate.original.body

def memoDriver : Driver MemoSource.Function where
  body := MemoSource.Certificate.original.body
  box := .boxNew
  entry := MemoSource.entryEvents
  run := MemoSource.sourceRun MemoSource.Certificate.original.body
  zero := by intros; rfl
  succ := by intros; rfl

theorem lookup_injective : Function.Injective lookupFunction := by
  intro first last he
  cases first <;> cases last <;> cases he <;> rfl

theorem memo_injective : Function.Injective memoFunction := by
  intro first last he
  cases first <;> cases last <;> cases he <;> rfl

theorem lookup_run (fuel : Nat) :
    CallsRefine lookupFunction (Control.run LookupSource.Certificate.original.body fuel)
      (SourceEval.run Certificate.original.body fuel) :=
  run_refines lookupDriver lookupFunction lookup_injective rfl
    (by intro function; cases function <;> decide)
    (by intro function; cases function <;> rfl) Certificate.original.body lookup_body fuel

theorem memo_run (fuel : Nat) :
    CallsRefine memoFunction (MemoSource.sourceRun MemoSource.Certificate.original.body fuel)
      (SourceEval.run Certificate.original.body fuel) :=
  run_refines memoDriver memoFunction memo_injective rfl
    (by intro function; cases function <;> decide)
    (by intro function; cases function <;> rfl) Certificate.original.body memo_body fuel

theorem lookup_normalized (fuel : Nat) (function : LookupSource.Function) (args : List Value)
    (hb : FieldsBounded args) {value : Value} {cost : LookupSource.Cost}
    (hr : LookupSource.run LookupSource.Program.body fuel function args = some (value, cost)) :
    SourceEval.run Certificate.original.body fuel (lookupFunction function) args = some (value, costMap cost) :=
  (lookup_run fuel function args value cost hb (by rwa [LookupSource.Certificate.original_run])).2

theorem memo_normalized (fuel : Nat) (function : MemoSource.Function) (args : List Value)
    (hb : FieldsBounded args) {value : Value} {cost : LookupSource.Cost}
    (hr : MemoSource.run MemoSource.Program.body fuel function args = some (value, cost)) :
    SourceEval.run Certificate.original.body fuel (memoFunction function) args = some (value, costMap cost) :=
  (memo_run fuel function args value cost hb (by rwa [MemoSource.Certificate.original_run])).2

theorem word_bounded (word : BalancedWord) : Bounded (encodeWord word) := by
  induction word with
  | Empty => exact .node .nil
  | Pair head tail ihHead ihTail => exact .node (.cons (.boxed ihHead) (.cons (.boxed ihTail) .nil))

theorem result_bounded (result : CommonEmbedding) : Bounded (encodeResult result) :=
  .node (.cons (word_bounded result.word) (.cons (.number result.edges.hmax) .nil))

theorem table_bounded (table : MemoTable) : Bounded (encodeTable table) := by
  induction table with
  | Empty => exact .node .nil
  | Entry entry rest ih =>
    exact .node (.cons (.boxed (.node (.cons (word_bounded entry.left)
      (.cons (word_bounded entry.right) (.cons (result_bounded entry.result) .nil))))) (.cons (.boxed ih) .nil))

theorem copy_source (word : BalancedWord) (fuel : Nat) (hf : wordHeight word ≤ fuel) :
    ∃ cost : LookupSource.Cost, SourceEval.run Certificate.original.body fuel .copyWord
      [.reference (encodeWord word)] = some (encodeWord word, costMap cost) ∧
      cost.events = (LookupEvents.copy word).2 := by
  obtain ⟨cost, hr, he⟩ := LookupSource.copy_source word fuel hf
  exact ⟨cost, lookup_normalized fuel .copyWord _ (.cons (.reference (word_bounded word)) .nil) hr, he⟩

theorem compare_source (left right : BalancedWord) (fuel : Nat) (hf : wordHeight left ≤ fuel) :
    ∃ cost : LookupSource.Cost, SourceEval.run Certificate.original.body fuel .compare
      [.reference (encodeWord left), .reference (encodeWord right)] =
      some (.boolean (LookupEvents.compare left right).1, costMap cost) ∧
      cost.events = ⟨0, (LookupEvents.compare left right).2, 0, 0, 0⟩ := by
  obtain ⟨cost, hr, he⟩ := LookupSource.compare_source left right fuel hf
  exact ⟨cost, lookup_normalized fuel .compare _
    (.cons (.reference (word_bounded left)) (.cons (.reference (word_bounded right)) .nil)) hr, he⟩

theorem copyResult_source (result : CommonEmbedding) (fuel : Nat) (hf : wordHeight result.word + 1 ≤ fuel) :
    ∃ cost : LookupSource.Cost, SourceEval.run Certificate.original.body fuel .copyResult
      [.reference (encodeResult result)] = some (encodeResult result, costMap cost) ∧
      cost.events = (LookupEvents.copyResult result).2 := by
  obtain ⟨cost, hr, he⟩ := LookupSource.copyResult_source result fuel hf
  exact ⟨cost, lookup_normalized fuel .copyResult _ (.cons (.reference (result_bounded result)) .nil) hr, he⟩

theorem lookup_source (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) :
    ∃ cost : LookupSource.Cost, SourceEval.run Certificate.original.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeOption (LookupEvents.lookup table left right).1, costMap cost) ∧
      cost.events = (LookupEvents.lookup table left right).2 := by
  obtain ⟨cost, hr, he⟩ := LookupSource.lookup_source table left right fuel hf
  exact ⟨cost, lookup_normalized fuel .lookup _ (.cons (.reference (table_bounded table))
    (.cons (.reference (word_bounded left)) (.cons (.reference (word_bounded right)) .nil))) hr, he⟩

theorem concatenate_source (left right : BalancedWord) (fuel : Nat)
    (hf : MemoSource.concatenateDepth left right ≤ fuel) :
    ∃ cost : LookupSource.Cost, SourceEval.run Certificate.original.body fuel .concatenate
      [.reference (encodeWord left), .reference (encodeWord right)] =
      some (encodeWord (OrderedSolver.appendWord left right), costMap cost) ∧
      cost.events = MemoSource.concatenateEvents left right := by
  obtain ⟨cost, hr, he⟩ := MemoSource.concatenate_source left right fuel hf
  exact ⟨cost, memo_normalized fuel .concatenate _
    (.cons (.reference (word_bounded left)) (.cons (.reference (word_bounded right)) .nil)) hr, he⟩

theorem insert_source (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : MemoSource.insertDepth left right result ≤ fuel) :
    ∃ cost : LookupSource.Cost, SourceEval.run Certificate.original.body fuel .insert
      [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
      some (encodeTable (.Entry ⟨left, right, result⟩ table), costMap cost) ∧
      cost.events = MemoSource.insertEvents left right result := by
  obtain ⟨cost, hr, he⟩ := MemoSource.insert_source table left right result fuel hf
  exact ⟨cost, memo_normalized fuel .insert _ (.cons (table_bounded table)
    (.cons (.reference (word_bounded left)) (.cons (.reference (word_bounded right))
      (.cons (.reference (result_bounded result)) .nil)))) hr, he⟩

end SubtreeProofs.Rust.SourceEval.Helpers
