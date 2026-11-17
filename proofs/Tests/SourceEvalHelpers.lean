import SubtreeProofs.Rust.SourceEvalHelperSafety

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource
open SubtreeProofs.Rust.SourceEval SubtreeProofs.Rust.SourceEval.Legacy
open verified_ordered_core

-- The numeric premise matters: the older profile accepts an over-wide scalar.
example : evalOperand (initialEnv [.number (2^32)]) (.copy (.local 1)) =
    some (.number (2^32), initialEnv [.number (2^32)]) := by rfl

example : SourceEval.operand (initialState [.number (2^32)]) (.copy (.local 1)) = none := by
  simp [SourceEval.operand, initialState, Partial.Locals.read_lift, readPlace, initialEnv]

-- Successful old runs embed; arbitrary failed old programs need not agree.
example : (Control.Action.dropConditional 1 : Control.Action LookupSource.Function).exec
    (fun _ _ => none) (initialEnv [.boolean true]) = none := by rfl

example : SourceEval.action (fun _ _ => none) (initialState [.boolean true]) (.drop 1) =
    some ((initialState [.boolean true]).set 1 .empty, Cost.local 1 ⟨1, 0⟩) := by
  simp [SourceEval.action_drop, initialState, Partial.Locals.lift, initialEnv, Partial.Slot.ofValue, Partial.Slot.dropWork]

-- Universal native consumers use the actual expanded program, and expose all
-- cost components rather than throwing away the returned cost.
example (left right : BalancedWord) :
    ∃ fuel cost, SourceEval.run SourceEval.Certificate.original.body fuel .concatenate
      [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      cost.work.events = MemoSource.concatenateEvents left right ∧ cost.destroyed = {} ∧ cost.solverCalls = 0 := by
  obtain ⟨cost, hr, he⟩ := SourceEval.Helpers.concatenate_source left right (MemoSource.concatenateDepth left right) (by rfl)
  exact ⟨_, costMap cost, hr, he, rfl, rfl⟩

example (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) :
    ∃ fuel cost, SourceEval.run SourceEval.Certificate.original.body fuel .insert
      [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), cost) ∧
      cost.work.events = MemoSource.insertEvents left right result ∧ cost.destroyed.boxes = 0 ∧ cost.solverCalls = 0 := by
  obtain ⟨cost, hr, he⟩ := SourceEval.Helpers.insert_source table left right result
    (MemoSource.insertDepth left right result) (by rfl)
  exact ⟨_, costMap cost, hr, he, rfl, rfl⟩

#check SourceEval.Helpers.lookup_source_scoped
#check SourceEval.Helpers.memo_source_scoped
#check SourceEval.Helpers.concatenate_source_total
#check SourceEval.Helpers.insert_source_total
