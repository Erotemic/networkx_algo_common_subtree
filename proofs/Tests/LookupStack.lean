import SubtreeProofs.Rust.LookupStackRefinement

/-! Explicit normal instruction fragments. These are not complete compiled
Rust crates or a claim of complete LLBC well-formedness. -/

namespace LookupStackTests

open SubtreeProofs.Rust.LookupSource Heap

private def returnTrue : Stack.Code := .step (.assign 0 (.use (.boolean true))) .ret
private def noStorage : Stack.Code := returnTrue
private def lateWrite : Stack.Code := .step (.storageLive 0) (.step (.storageDead 0) returnTrue)

private def view (code : Stack.Code) : Option Bool :=
  match Heap.exec (fun _ _ _ => none) code.erase [] (initialLocals []) with
  | some (.returned (.boolean value), _, _) => some value
  | _ => none

-- Old reset-only execution allows writes into never-allocated/dead storage.
example : view noStorage = some true := by decide +kernel
example : view lateWrite = some true := by decide +kernel
example : Stack.verify noStorage (Stack.initial 1 0) (fun _ => false) = false := by decide +kernel
example : Stack.verify lateWrite (Stack.initial 1 0) (fun _ => false) = false := by decide +kernel

-- Reallocating an already allocated plain slot is allowed by the pinned source.
private def reallocate : Stack.Code := .step (.storageLive 0)
  (.step (.assign 0 (.use (.boolean true))) (.step (.storageLive 0)
    (.step (.assign 0 (.use (.boolean false))) .ret)))
example : view reallocate = some false := by decide +kernel
example : Stack.verify reallocate (Stack.initial 1 0) (fun _ => false) = true := by decide +kernel

-- Repeated deallocation is permitted. A moved value leaves live empty storage.
example : Stack.inferAction [.full, .dead] (.storageDead 1) = some [.full, .dead] := by decide +kernel
example : Stack.inferOperand [.full] (.move 0) = some [.empty] := by decide +kernel
example : Stack.inferOperand [.empty] (.move 0) = none := by decide +kernel
example : Stack.inferOperand [.dead] (.copy (.local 0)) = none := by decide +kernel
example : Stack.inferRValue [.empty] (.address (.local 0)) = none := by decide +kernel

example : Stack.inferAction [.empty] (.dropConditional 0) = some [.empty] := by decide +kernel
example : Stack.inferAction [.full] (.dropConditional 0) = none := by decide +kernel
example : Stack.inferAction [.full] (.call .compare [.boolean true] 0) = none := by decide +kernel

-- Every branch must leave a destination allocated before the common write.
private def branchDead : Stack.Code := .step (.storageLive 0)
  (.branch (.value (.boolean false)) (.boolean true) none
    .done (.step (.storageDead 0) .done) returnTrue)
example : view branchDead = some true := by decide +kernel
example : Stack.verify branchDead (Stack.initial 1 0) (fun _ => false) = false := by decide +kernel

private def earlyReturn : Stack.Code := .step (.storageLive 0)
  (.step (.assign 0 (.use (.boolean true)))
    (.branch (.value (.boolean true)) (.boolean true) none .ret .ret lateWrite))
example : view earlyReturn = some true := by decide +kernel
example : Stack.verify earlyReturn (Stack.initial 1 0) (fun _ => false) = true := by decide +kernel

example {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body 2 .copyWord [.shared ⟨0, []⟩] [.node .word 0 []] = some (cell, after, cost)) :
    Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount 2 .copyWord
      [.shared ⟨0, []⟩] [.node .word 0 []] cell after cost :=
  Stack.Certificate.original_run_safe 2 .copyWord _ _ rfl hr

example : Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount 1 .boxNew
    [.boolean true] [] (.owned 0) [.boolean true] ⟨1, entryEvents .boxNew⟩ :=
  Stack.Certificate.original_run_safe 1 .boxNew _ _ rfl rfl

example : Stack.StateRep (Stack.close [.full, .empty, .dead]) (fun _ => none) := Stack.closed_frame _

end LookupStackTests
