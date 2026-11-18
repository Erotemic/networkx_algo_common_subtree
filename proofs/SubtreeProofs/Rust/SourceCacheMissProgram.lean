module

public import SubtreeProofs.Rust.SourceCacheHitScope
public import SubtreeProofs.Rust.SourceWordLoanCells
import Mathlib.Tactic.IntervalCases

/-! The actual cache-miss setup and native word routing. These identities keep
all source branches and their real continuations intact. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def missSetupActions : List Action :=
  [.drop 4, .storageDead 6, .storageDead 4, .storageLive 13, .storageLive 14,
   .assign 14 (.use (.copy (.local 1))), .storageLive 15,
   .assign 15 (.use (.copy (.local 2))),
   .assign 13 (.aggregate .tuple 0 [.move (.local 14), .move (.local 15)]),
   .storageDead 15, .storageDead 14]

def missCases : Code := .switch (.discriminant (.deref (.field (.local 13) none 0)))
  [(.variant .word 0, 0)] (some 1) emptyLeft rightCases .done

def missCode (index : Nat) : Code := (missSetupActions.drop index).foldr Control.Tree.step missCases

theorem cacheMiss_actions : cacheMiss = missSetupActions.foldr Control.Tree.step missCases := rfl

theorem emptyRight_eq_emptyLeft : emptyRight = emptyLeft := rfl

def queryTuple (left right : BalancedWord) : Slot :=
  .node .tuple 0 [.shared (encodeWord left), .shared (encodeWord right)]

def wordKey : BalancedWord → Key
  | .Empty => .variant .word 0
  | .Pair _ _ => .variant .word 1

theorem miss_observes_queries (index : Nat) (bound : index ≤ 11) (slot : Nat) (member : slot ∈ [1, 2]) :
    LoanEnding.endsBeforeObservation slot (missCode index) = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> interval_cases index <;> decide +kernel

theorem queryTuple_words (left right : BalancedWord) : WordLoans (queryTuple left right) :=
  .node (.cons (.shared left) (.cons (.shared right) .nil))

theorem queryTuple_typed (left right : BalancedWord) :
    SlotTyped (queryTuple left right) (.tuple [.shared (.adt .word), .shared (.adt .word)]) :=
  .node (.tuple _) (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil))

theorem miss_scrutinee_source {state : State} (left right : BalancedWord) (tuple : state 13 = queryTuple left right) :
    SourceEval.scrutinee state (.discriminant (.deref (.field (.local 13) none 0))) = some (wordKey left, state) := by
  cases left <;> simp [SourceEval.scrutinee, splitPlace, tuple, queryTuple, Slot.get, wordKey, encodeWord, Slot.ofValue]

end SubtreeProofs.Rust.SourceEval.Evaluator
