import SubtreeProofs.Complexity.EditDistance.Clients

namespace EditDistanceTests

open SubtreeProofs.Complexity.Memo
open SubtreeProofs.Complexity.EditDistance

private structure Observation where
  values : List Nat
  setup : Nat
  calls : Nat
  expansions : Nat
  reads : Nat
  writes : Nat
  localWork : Nat
  deriving DecidableEq

private def observe (result : Nat × EStateM.Result Unit (EvalState QueryKey Storage) (List Nat)) :
    Option Observation :=
  match result.2 with
  | .error _ _ => none
  | .ok values final => some ⟨values, result.1, Event.calls final.events,
      (Event.completedKeys final.events).length, Event.lookupWork final.events,
      Event.insertionWork final.events, Event.localWork final.events⟩

example : distance ([] : List Char) [] = 0 := by decide +kernel
example : distance [] "ab".toList = 2 := by decide +kernel
example : distance "ab".toList [] = 2 := by decide +kernel
example : distance "cat".toList "cut".toList = 1 := by decide +kernel
example : distance "ab".toList "ba".toList = 2 := by decide +kernel

-- Independent edit witness: copy, replacement, copy.
example : Edits "cat".toList "cut".toList 1 :=
  .copy 'c' (.replace 'a' 'u' (.copy 't' .empty))

example (cost : Nat) (he : Edits "cat".toList "cut".toList cost) : 1 ≤ cost := by
  have h := distance_le_edits he
  simpa only [show distance "cat".toList "cut".toList = 1 by decide +kernel] using h

-- Equal result/combinatorics; actual representation and setup counters differ.
example : observe (runList ['x'] ['y'] [(0, 0)]) = some ⟨[1], 1, 4, 4, 3, 4, 5⟩ := by
  decide +kernel

example : observe (runDense ['x'] ['y'] [(0, 0)]) = some ⟨[1], 5, 4, 4, 12, 12, 5⟩ := by
  decide +kernel

-- A duplicate root contributes a lookup, without another expansion.
example : observe (runList ['x'] ['y'] [(0, 0), (0, 0)]) = some ⟨[1, 1], 1, 5, 4, 4, 4, 5⟩ := by
  decide +kernel

example : observe (runDense ['x'] ['y'] [(0, 0), (0, 0)]) = some ⟨[1, 1], 5, 5, 4, 15, 12, 5⟩ := by
  decide +kernel

-- Boundary-only input still pays for the entire dense table setup.
example : observe (runList [] ['a', 'b'] [(0, 0)]) = some ⟨[2], 1, 1, 1, 0, 1, 0⟩ := by
  decide +kernel

example : observe (runDense [] ['a', 'b'] [(0, 0)]) = some ⟨[2], 4, 1, 1, 3, 3, 0⟩ := by
  decide +kernel

example : observe (runList ['x'] ['y'] []) = some ⟨[], 1, 0, 0, 0, 0, 0⟩ := by decide +kernel
example : observe (runDense ['x'] ['y'] []) = some ⟨[], 5, 0, 0, 0, 0, 0⟩ := by decide +kernel

-- A table from changed frozen inputs is unsound, despite identical index sizes.
example : ¬ (ListCache.ops : CacheOps (Key ['x'] ['y']) Nat _).Sound (value ['x'] ['y']) [((0, 0), 0)] := by
  intro hs
  have he := hs (0, 0) 0 (by decide +kernel)
  have hn : 0 ≠ value ['x'] ['y'] (0, 0) := by decide +kernel
  exact hn he

end EditDistanceTests
