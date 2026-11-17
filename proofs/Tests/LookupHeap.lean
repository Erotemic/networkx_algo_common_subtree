import SubtreeProofs.Rust.LookupHeapRefinement
import SubtreeProofs.Rust.LookupHeapInputs
import SubtreeProofs.Rust.LookupHeapReturnOwnership

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace LookupHeapTests

open verified_ordered_core SubtreeProofs.Rust.LookupSource
open SubtreeProofs.Rust.LookupSource.Heap

private def pairMemory : Memory :=
  [.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1]]

private def env : Locals := initialLocals [.shared ⟨2, []⟩]

-- The second dereference follows a Box cell rather than copying its payload.
example : locate pairMemory env (.deref (.field (.deref (.local 1)) (some 1) 0)) =
    some (.node .word 0 [], some ⟨0, []⟩) := rfl

example : borrow pairMemory env (.field (.deref (.local 1)) (some 1) 0) =
    some (.shared ⟨2, [0]⟩) := rfl

-- Borrowing the stack slot is outside this heap-only fragment.
example : borrow pairMemory env (.local 1) = none := rfl

example : locate pairMemory env (.field (.deref (.local 1)) (some 0) 0) = none := rfl
example : locate pairMemory env (.field (.deref (.local 1)) (some 1) 2) = none := rfl
example : read pairMemory ⟨20, []⟩ = none := rfl
example : read pairMemory ⟨2, [3]⟩ = none := rfl

example : operands pairMemory [.move 1, .move 1] env = none := rfl
example : operand pairMemory (initialLocals [.owned 0]) (.copy (.local 1)) = none := rfl
example : action (fun _ _ _ => none) pairMemory (initialLocals [.owned 0]) (.dropMoved 1) = none := rfl

private def viewBool (result : Option (Cell × Memory × Cost)) : Option (Bool × Nat × Nat × Nat) :=
  match result with
  | some (.boolean value, memory, cost) =>
    some (value, memory.length, cost.events.compareNodes, cost.events.allocations)
  | _ => none

-- Both query arguments can share the same heap address. No allocation occurs.
example : viewBool (Heap.run Program.body 2 .compare
    [.shared ⟨2, []⟩, .shared ⟨2, []⟩] pairMemory) = some (true, 3, 3, 0) := by
  decide +kernel

private def viewWord (result : Option (Cell × Memory × Cost)) : Option (Nat × Nat × Nat × Nat) :=
  match result with
  | some (.node .word 1 [.owned head, .owned tail], memory, cost) =>
    some (head, tail, memory.length, cost.events.allocations)
  | _ => none

-- Copying allocates fresh children and retains every preexisting cell.
example : viewWord (Heap.run Program.body 2 .copyWord [.shared ⟨2, []⟩] pairMemory) =
    some (3, 4, 5, 2) := by decide +kernel

private def table : MemoTable := .Entry ⟨.Empty, .Empty, ⟨.Pair .Empty .Empty, 7#u32⟩⟩ .Empty
private def packed : Cell × Memory := packTable table []
private def tableRoot : Cell × Memory := shareRoot packed.2 packed.1
private def queryRoot : Cell × Memory := shareRoot tableRoot.2 (.node .word 0 [])

private def viewHit (result : Option (Cell × Memory × Cost)) :
    Option (Nat × Nat × Nat × Nat × Nat × Nat) :=
  match result with
  | some (.node .optional 1 [.node .embedding 0
      [.node .word 1 [.owned head, .owned tail], .number edges]], memory, cost) =>
    some (edges, head, tail, memory.length, cost.events.allocations, cost.events.compareNodes)
  | _ => none

-- The aliased empty queries hit an oversized cached witness. Full owned copy
-- costs and fresh output addresses survive; no cache soundness is assumed.
example : viewHit (Heap.run Program.body 8 .lookup
    [tableRoot.1, queryRoot.1, queryRoot.1] queryRoot.2) = some (7, 6, 7, 8, 2, 2) := by
  decide +kernel

private def viewMiss (result : Option (Cell × Memory × Cost)) : Option (Nat × Nat) :=
  match result with
  | some (.node .optional 0 [], _, cost) => some (cost.events.compareNodes, cost.events.allocations)
  | _ => none

example : viewMiss (Heap.run Program.body 3 .lookup
    [.shared ⟨0, []⟩, .shared ⟨1, []⟩, .shared ⟨1, []⟩]
    [.node .table 0 [], .node .word 0 []]) = some (0, 0) := rfl

example : viewMiss (Heap.run ExtraCompare.body 3 .lookup
    [.shared ⟨0, []⟩, .shared ⟨1, []⟩, .shared ⟨1, []⟩]
    [.node .table 0 [], .node .word 0 []]) = some (1, 0) := rfl

-- All input representations exist, including arbitrary warm immutable cells.
example (table : MemoTable) (left right : BalancedWord) (memory : Memory) :
    ∃ args after, RepresentsFields after args
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] ∧
      Extends memory after := inputs_exist table left right memory

private def aliasWord : Cell := .node .word 1 [.owned 0, .owned 0]
private def aliasMemory : Memory := [.node .word 0 []]

-- Typing and snapshot readback deliberately allow this duplicated Box alias.
example : Represents aliasMemory aliasWord (encodeWord (.Pair .Empty .Empty)) :=
  .node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))

example : Typed aliasMemory aliasWord (.adt .word) :=
  .node .pairWord (.cons (.owned rfl (.node .emptyWord .nil))
    (.cons (.owned rfl (.node .emptyWord .nil)) .nil))

private theorem alias_footprint : Footprint aliasMemory aliasWord [0, 0] :=
  .node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))

-- An ownership-occurrence list retains both occurrences; a set would hide one.
example (start stop : Nat) : ¬Owns aliasMemory aliasWord start stop := by
  intro ho
  have hn := (ho.exclusive alias_footprint).2.1
  have hbad : ¬([0, 0] : List Nat).Nodup := by decide +kernel
  exact hbad hn

-- Reusing an old input Box cannot pass a fresh-output ownership interval.
example (stop : Nat) : ¬Owns aliasMemory (.owned 0) 1 stop := by
  intro ho
  have hf : Footprint aliasMemory (.owned 0) [0] := .owned rfl (.node .nil)
  have hi := ((ho.exclusive hf).2.2 0).mp (by simp)
  omega

-- An unused newly allocated cell cannot disappear from the returned ledger.
example : ¬Owns [.node .word 0 [], .node .word 0 []] (.owned 0) 0 2 := by
  intro ho
  have hf : Footprint [.node .word 0 [], .node .word 0 []] (.owned 0) [0] := .owned rfl (.node .nil)
  have he := (ho.exclusive hf).1
  have hbad : ([0] : List Nat) ≠ List.range' 0 (2 - 0) := by decide +kernel
  exact hbad he

end LookupHeapTests
