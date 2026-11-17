import SubtreeProofs.Rust.LookupTypeRefinement
import SubtreeProofs.Rust.LookupFrameChecker

namespace LookupTypePreservationTests

open SubtreeProofs.Rust.LookupSource Heap SourceTypes

-- A genuinely typed shared input may contain duplicate owned aliases.
-- Type preservation therefore has no hidden spatial-uniqueness premise.
private def memory : Memory :=
  [.node .word 0 [], .node .word 1 [.owned 0, .owned 0]]

private theorem input_typed : Typed memory (.shared ⟨1, []⟩) (.shared (.adt .word)) :=
  .shared rfl (.node .pairWord
    (.cons (.owned rfl (.node .emptyWord .nil))
      (.cons (.owned rfl (.node .emptyWord .nil)) .nil)))

example {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body 2 .copyWord [.shared ⟨1, []⟩] memory = some (cell, after, cost)) :
    Typed after cell (.adt .word) :=
  (original_run_typed 2 .copyWord _ [.shared (.adt .word)] memory cell after cost (.adt .word)
    (.cons input_typed .nil) (by simp [callOutput, inputs, output, sameList_refl]) hr).1

private def viewCopy : Option (Nat × Nat × Nat) :=
  match Heap.run Program.body 2 .copyWord [.shared ⟨1, []⟩] memory with
  | some (.node .word 1 [.owned head, .owned tail], after, _) => some (head, tail, after.length)
  | _ => none

-- Success is checked separately: the actual copy allocates distinct children.
example : viewCopy = some (2, 3, 4) := by decide +kernel

example : Typed [.boolean true] (.owned 0) (.owned .boolean) :=
  (original_run_typed 1 .boxNew [.boolean true] [.boolean] [] (.owned 0) [.boolean true]
    ⟨1, entryEvents .boxNew⟩ (.owned .boolean) (.cons (.boolean true) .nil) rfl rfl).1

example {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run ExtraCompare.body 3 .lookup
      [.shared ⟨0, []⟩, .shared ⟨1, []⟩, .shared ⟨1, []⟩]
      [.node .table 0 [], .node .word 0 []] = some (cell, after, cost)) :
    Typed after cell (.adt .optional) :=
  (mutant_run_typed 3 .lookup _ (inputs .lookup) _ cell after cost (.adt .optional)
    (.cons (.shared rfl (.node .emptyTable .nil))
      (.cons (.shared rfl (.node .emptyWord .nil))
        (.cons (.shared rfl (.node .emptyWord .nil)) .nil))) (by simp [callOutput, sameList_refl, output]) hr).1

-- Static types alone do not imply initialization or successful variant reads.
example : checkCode [.adt .word] (.adt .word) .ret = true := by decide +kernel
example : Heap.exec (fun _ _ _ => none) .ret [] (initialLocals []) = none := rfl

private def guardedField : Place := .field (.local 0) (some 1) 0
example : inferPlace [.adt .word] guardedField = some (.owned (.adt .word)) := rfl
example : locate [] (fun _ => some (.node .word 0 [])) guardedField = none := rfl

-- Clearing a live owner preserves types, but fails the ownership-class guard.
example : checkAction [.owned (.adt .word)] (.scope 0) = true := rfl
example : Frame.inferAction [some true] (.scope 0) = none := rfl

end LookupTypePreservationTests
