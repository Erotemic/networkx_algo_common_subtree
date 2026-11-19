module

public import SubtreeProofs.Rust.SourceEmptyMissProgram
public import SubtreeProofs.Rust.SourceOriginalBorrowView
public import SubtreeProofs.Rust.SourcePrefixObserved
import Mathlib.Tactic.IntervalCases

/-! The pinned pair/pair head-call prefix and its native boxed-child views.
All continuations retain actual source control, including the early head
failure and the subsequent tail recursion. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def headCases : Code := .switch (.discriminant (.local 31)) [(.variant .optional 0, 0), (.variant .optional 1, 1)] none headsFailure recurseTails cleanupInputs

def headActions : List Action :=
  [.storageLive 27, .assign 27 (.address (.field (.deref (.field (.local 13) none 0)) (some 1) 0)),
   .storageLive 28, .assign 28 (.address (.field (.deref (.field (.local 13) none 0)) (some 1) 1)),
   .storageLive 29, .assign 29 (.address (.field (.deref (.field (.local 13) none 1)) (some 1) 0)),
   .storageLive 30, .assign 30 (.address (.field (.deref (.field (.local 13) none 1)) (some 1) 1)),
   .storageLive 33, .storageLive 34, .assign 34 (.address (.deref (.deref (.local 27)))),
   .storageLive 35, .assign 35 (.address (.deref (.deref (.local 29)))),
   .storageLive 36, .assign 36 (.use (.move (.local 3))),
   .call .evaluate [.move (.local 34), .move (.local 35), .move (.local 36)] 33,
   .storageDead 36, .storageDead 35, .storageDead 34,
   .storageLive 31, .assign 31 (.use (.move (.field (.local 33) none 0))),
   .storageLive 32, .assign 32 (.use (.move (.field (.local 33) none 1))),
   .drop 33, .storageDead 33, .storageLive 37]

def headCode (index : Nat) : Code := (headActions.drop index).foldr Control.Tree.step headCases

theorem recurseHeads_actions : recurseHeads = headActions.foldr Control.Tree.step headCases := rfl

def pairFieldPlace (side child : Nat) : Place := .field (.deref (.field (.local 13) none side)) (some 1) child

def pairChild (lh lt rh rt : BalancedWord) (side child : Nat) : BalancedWord :=
  if side = 0 then (if child = 0 then lh else lt) else (if child = 0 then rh else rt)

theorem pair_field_route {state : State} {lh lt rh rt : BalancedWord}
    (tuple : state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)) (side child : Nat) (sideBound : side ∈ [0, 1]) :
    SharedRoute (state 13) [.field none side, .deref, .field (some 1) child] := by
  rw [tuple]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sideBound
  rcases sideBound with rfl | rfl <;>
    exact SharedRoute.field rfl rfl (.shared _ _)

theorem pair_field_source {state : State} {lh lt rh rt : BalancedWord}
    (tuple : state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)) (side child : Nat)
    (sideBound : side ∈ [0, 1]) (childBound : child ∈ [0, 1]) :
    state.read (pairFieldPlace side child) = some (.boxed (encodeWord (pairChild lh lt rh rt side child))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sideBound childBound
  rcases sideBound with rfl | rfl <;> rcases childBound with rfl | rfl <;>
    simp [Partial.Locals.read, pairFieldPlace, splitPlace, tuple, queryTuple, Slot.read, Slot.get, encodeWord, Slot.ofValue,
      ofFields, Slot.materialize, pairChild, Slot.materialize_ofValue]

theorem head_observes_fields (slot : Nat) (member : slot ∈ [27, 28, 29, 30]) :
    LoanEnding.endsBeforeObservation slot (headCode 8) = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide +kernel

end SubtreeProofs.Rust.SourceEval.Evaluator
