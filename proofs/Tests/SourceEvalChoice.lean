import SubtreeProofs.Rust.SourceEvalChoiceRefinement

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource SubtreeProofs.Rust.LookupSource.Partial
open SubtreeProofs.Rust.SourceEval verified_ordered_core

private def emptyZero : CommonEmbedding := ⟨.Empty, 0#u32⟩
private def pairZero : CommonEmbedding := ⟨.Pair .Empty .Empty, 0#u32⟩
private def emptyOne : CommonEmbedding := ⟨.Empty, 1#u32⟩

-- A tie between distinct witnesses retains the first and destroys the second.
example : run Certificate.original.body 1 .chooseLonger [encodeResult emptyZero, encodeResult pairZero] =
    some (encodeResult emptyZero, ⟨⟨34, {}⟩, ⟨7, 2⟩, 0⟩) := by
  simpa [emptyZero, pairZero, Choice.cost, Choice.destroyed, Choice.loser, OrderedSolver.selectResult,
    encodeResult, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
    using Choice.source_run 0 emptyZero pairZero

-- Stored scores need not equal word sizes. Drop work follows the losing word.
example : run Certificate.original.body 1 .chooseLonger [encodeResult pairZero, encodeResult emptyOne] =
    some (encodeResult emptyOne, ⟨⟨34, {}⟩, ⟨7, 2⟩, 0⟩) := by
  simpa [pairZero, emptyOne, Choice.cost, Choice.destroyed, Choice.loser, OrderedSolver.selectResult,
    encodeResult, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
    using Choice.source_run 0 pairZero emptyOne

example (first second : CommonEmbedding) :
    ∃ result, choose_longer first second = .ok result ∧
      Certificate.executeSource Input.Program.source 512 1 .chooseLonger [encodeResult first, encodeResult second] =
        .ok (some (encodeResult result, Choice.cost first second)) ∧
      (Choice.cost first second).work.events.allocations = 0 ∧ (Choice.cost first second).solverCalls = 0 :=
  ⟨_, OrderedSolver.choose_longer_correct first second, Choice.source_execute 0 first second, rfl, rfl⟩

#check Choice.first_on_tie
#check Choice.cost_exact
