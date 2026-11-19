import SubtreeProofs.Rust.LookupFrameRefinement

namespace LookupFrameTests

open SubtreeProofs.Rust.LookupSource
open SubtreeProofs.Rust.LookupSource.Heap
open SubtreeProofs.Rust.LookupSource.Heap.Frame

private def accepts (code : Code) (output : Bool := false) : Bool :=
  verify code (initialState 6 []) output (fun _ => false)

private def allocated (rest : Code) : Code :=
  .step (.call .boxNew [.boolean false] 1) rest

-- These instruction fragments deliberately violate frame safety. They are
-- not claimed to be complete typed LLBC crates or compiled Rust mutations.
private def badReset : Code := allocated (.step (.scope 1)
  (.step (.assign 0 (.use (.boolean true))) .ret))

private def badOverwrite : Code := allocated (.step (.assign 1 (.use (.boolean false)))
  (.step (.assign 0 (.use (.boolean true))) .ret))

private def badReturn : Code := allocated (.step (.assign 0 (.use (.boolean true))) .ret)

example : accepts badReset = false := by decide +kernel
example : accepts badOverwrite = false := by decide +kernel
example : accepts badReturn = false := by decide +kernel

private def observe (code : Code) : Option (Bool × Nat × Nat) :=
  match Heap.exec (Heap.run Program.body 1) code [] (initialLocals []) with
  | some (.returned (.boolean value), memory, cost) => some (value, memory.length, cost.events.allocations)
  | _ => none

-- The old unguarded interpreter can still return the expected Boolean. The
-- additional certificate detects the unsafe intermediate local destruction.
example : observe badReset = some (true, 1, 1) := by decide +kernel
example : observe badOverwrite = some (true, 1, 1) := by decide +kernel
example : observe badReturn = some (true, 1, 1) := by decide +kernel

-- Moving the owned local to the return slot empties its source and is accepted.
private def movedReturn : Code := allocated (.step (.assign 0 (.use (.move 1))) (.step (.scope 1) .ret))
example : accepts movedReturn true = true := by decide +kernel

-- A second move of the same local cannot reuse its ownership.
example : accepts (allocated (.step (.assign 2 (.use (.move 1)))
    (.step (.assign 0 (.use (.move 1))) .ret))) true = false := by decide +kernel

-- Borrow-only helpers cannot receive a potentially owned value by move.
example : accepts (allocated (.step (.call .copyWord [.move 1] 0) .ret)) true = false := by decide +kernel

-- Tuples containing only non-owning values can be cleared before return.
example : accepts (.step (.assign 1 (.aggregate .tuple 0 [.boolean false, .boolean true]))
    (.step (.scope 1) (.step (.assign 0 (.use (.boolean true))) .ret))) = true := by decide +kernel

-- The first arm returns early; the second must satisfy the common continuation.
example : accepts (.branch (.value (.boolean true)) (.boolean true) none
    (.step (.assign 0 (.use (.boolean true))) .ret) .done
    (.step (.assign 0 (.use (.boolean false))) .ret)) = true := by decide +kernel

-- A live owner on either fallthrough path rejects the shared reset.
example : accepts (.branch (.value (.boolean true)) (.boolean true) none
    (allocated .done) .done
    (.step (.scope 1) (.step (.assign 0 (.use (.boolean true))) .ret))) = false := by decide +kernel

example : Frame.BodyChecked Program.body 20 := Frame.original_checked
example : Frame.BodyChecked ExtraCompare.body 20 := Frame.mutant_checked

end LookupFrameTests
