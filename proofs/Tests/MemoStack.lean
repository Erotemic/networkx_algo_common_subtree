import SubtreeProofs.Rust.MemoStackRefinement

/-! Normal source fragments distinguish allocation from reset-only execution.
These checks exercise memo callee arities and actual recursive certificates. -/

namespace MemoStackTests

open SubtreeProofs.Rust LookupSource LookupSource.Heap

private def returnTrue : MemoSource.Stack.Code := .step (.assign 0 (.use (.boolean true))) .ret
private def noStorage : MemoSource.Stack.Code := returnTrue
private def lateWrite : MemoSource.Stack.Code := .step (.storageLive 0) (.step (.storageDead 0) returnTrue)

private def view (code : MemoSource.Stack.Code) : Option Bool :=
  match Heap.exec (fun _ _ _ => none) code.erase [] (initialLocals []) with
  | some (.returned (.boolean value), _, _) => some value
  | _ => none

-- Successful reset-only execution alone does not prove source storage safety.
example : view noStorage = some true := by decide +kernel
example : view lateWrite = some true := by decide +kernel
example : Stack.verifyWith MemoSource.arity noStorage (Stack.initial 1 0) (fun _ => false) = false := by decide +kernel
example : Stack.verifyWith MemoSource.arity lateWrite (Stack.initial 1 0) (fun _ => false) = false := by decide +kernel

-- Callee arities are supplied by the memo profile, including the owned table.
example : Stack.inferActionWith MemoSource.arity [.empty]
    (.call .insert [.boolean true, .boolean true, .boolean true] 0) = none := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.empty]
    (.call .insert [.boolean true, .boolean true, .boolean true, .boolean true] 0) = some [.full] := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.dead]
    (.call .concatenate [.boolean true, .boolean true] 0) = none := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.empty]
    (.call .concatenate [.boolean true, .boolean true] 0) = some [.full] := by decide +kernel

-- Moving leaves allocated empty storage. Repeated markers match pinned Charon.
example : Stack.inferOperand [.full] (.move 0) = some [.empty] := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.empty] (.assign 0 (.use (.boolean true))) = some [.full] := by decide +kernel
example : Stack.inferOperand [.empty] (.move 0) = none := by decide +kernel
example : Stack.inferRValue [.empty] (.address (.local 0)) = none := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.empty] (.storageLive 0) = some [.empty] := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.dead] (.storageDead 0) = some [.dead] := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.full] (.dropConditional 0) = none := by decide +kernel
example : Stack.inferActionWith MemoSource.arity [.full] (.storageLive 1) = none := by decide +kernel

private def branchDead : MemoSource.Stack.Code := .step (.storageLive 0)
  (.branch (.value (.boolean false)) (.boolean true) none
    .done (.step (.storageDead 0) .done) returnTrue)
example : view branchDead = some true := by decide +kernel
example : Stack.verifyWith MemoSource.arity branchDead (Stack.initial 1 0) (fun _ => false) = false := by decide +kernel

private def earlyReturn : MemoSource.Stack.Code := .step (.storageLive 0)
  (.step (.assign 0 (.use (.boolean true)))
    (.branch (.value (.boolean true)) (.boolean true) none .ret .ret lateWrite))
example : Stack.verifyWith MemoSource.arity earlyReturn (Stack.initial 1 0) (fun _ => false) = true := by decide +kernel

example {cell : Cell} {after : Memory} {cost : Cost}
    (hr : MemoSource.Heap.run MemoSource.Program.body 2 .copyWord [.shared ⟨0, []⟩]
      [.node .word 0 []] = some (cell, after, cost)) :
    MemoSource.Stack.RunSafe MemoSource.Stack.Certificate.original MemoSource.Stack.Certificate.originalCount
      2 .copyWord [.shared ⟨0, []⟩] [.node .word 0 []] cell after cost :=
  MemoSource.Stack.Certificate.original_run_safe 2 .copyWord _ _ rfl hr

example : MemoSource.Stack.RunSafe MemoSource.Stack.Certificate.original MemoSource.Stack.Certificate.originalCount
    1 .boxNew [.boolean true] [] (.owned 0) [.boolean true] ⟨1, MemoSource.entryEvents .boxNew⟩ :=
  MemoSource.Stack.Certificate.original_run_safe 1 .boxNew _ _ rfl rfl

example : (Stack.initial (MemoSource.Stack.Certificate.originalCount .insert) (MemoSource.arity .insert)).length = 15 :=
  MemoSource.Stack.Certificate.original_initial_length .insert (by decide)

open verified_ordered_core in
example : ∃ cell after cost,
    MemoSource.Heap.run MemoSource.Program.body 2 .concatenate [.shared ⟨0, []⟩, .shared ⟨0, []⟩]
      [.node .word 0 []] = some (cell, after, cost) ∧
    MemoSource.Stack.RunSafe MemoSource.Stack.Certificate.original MemoSource.Stack.Certificate.originalCount
      2 .concatenate [.shared ⟨0, []⟩, .shared ⟨0, []⟩] [.node .word 0 []] cell after cost := by
  obtain ⟨cell, after, cost, _, hr, hs, _⟩ := MemoSource.Stack.concatenate_stack_total .Empty .Empty
    2 (by decide +kernel) [.node .word 0 []] ⟨0, []⟩ ⟨0, []⟩ (.shared rfl (.node .nil)) (.shared rfl (.node .nil))
  exact ⟨cell, after, cost, hr, hs⟩

private def word : Cell := .node .word 0 []
private def memory : Memory := [word, .node .embedding 0 [word, .number 77]]

open verified_ordered_core in
example : ∃ cell after cost,
    MemoSource.Heap.run MemoSource.Program.body 4 .insert
      [.node .table 0 [], .shared ⟨0, []⟩, .shared ⟨0, []⟩, .shared ⟨1, []⟩] memory = some (cell, after, cost) ∧
    MemoSource.Stack.RunSafe MemoSource.Stack.Certificate.original MemoSource.Stack.Certificate.originalCount
      4 .insert [.node .table 0 [], .shared ⟨0, []⟩, .shared ⟨0, []⟩, .shared ⟨1, []⟩] memory cell after cost := by
  obtain ⟨cell, after, cost, _, hr, hs, _⟩ := MemoSource.Stack.insert_stack_total .Empty .Empty .Empty ⟨.Empty, 77#u32⟩
    4 (by decide +kernel) memory (.node .table 0 []) ⟨0, []⟩ ⟨0, []⟩ ⟨1, []⟩ (.node .nil)
      (.shared rfl (.node .nil)) (.shared rfl (.node .nil))
      (.shared rfl (.node (.cons (.node .nil) (.cons (.number 77) .nil))))
  exact ⟨cell, after, cost, hr, hs⟩

end MemoStackTests
