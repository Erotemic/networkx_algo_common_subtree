import SubtreeProofs.Rust.SourcePartialLocals

/-! Partial field moves required by the actual evaluator. These are source
storage fragments, not compiled Rust mutants or a full evaluator certificate. -/

namespace SourcePartialTests

open SubtreeProofs.Rust.LookupSource Partial

private def emptyWord : Value := .node .word 0 []
private def word : Value := .node .word 1 [.boxed emptyWord, .boxed emptyWord]
private def tuple : Slot := .node .tuple 0 [Slot.ofValue word, .number 77]
private def rest : Slot := .node .tuple 0 [.empty, .number 77]
private def first : List Projection := [.field none 0]

-- Moving one field retains the enclosing constructor and initialized sibling.
example : tuple.take first = some (word, rest) := by
  simp [tuple, first, rest, Slot.take, Slot.materialize_ofValue]
example : rest.get [] = some rest := rfl
example : rest.read [.field none 1] = some (.number 77) := by
  simp [rest, Slot.read, Slot.get, Slot.materialize]
example : rest.read [] = none := by decide +kernel
example : rest.take [] = none := by decide +kernel
example : rest.take first = none := by decide +kernel
example : rest.take [.field none 1] = some (.number 77, .node .tuple 0 [.empty, .empty]) := by
  simp [rest, Slot.take, Slot.materialize]
example : tuple.take [.field none 8] = none := by decide +kernel
example : tuple.take [.field (some 1) 0] = none := by decide +kernel

-- Box owners transferred to the result are absent from the remaining drop.
example : tuple.dropWork = ⟨7, 2⟩ := by decide +kernel
example : rest.dropWork = ⟨2, 0⟩ := by decide +kernel
example : tuple.dropWork = (Slot.ofValue word).dropWork.plus rest.dropWork :=
  tuple.take_work first (by simp [tuple, first, rest, Slot.take, Slot.materialize_ofValue])

-- Moving the payload out of a Box leaves its owner shell to be destroyed.
private def box : Slot := .boxed (Slot.ofValue word)
example : box.take [.deref] = some (word, .boxed .empty) := by simp [box, Slot.take, Slot.materialize_ofValue]
example : (Slot.boxed .empty).dropWork = ⟨1, 1⟩ := by decide +kernel
example : (Slot.boxed .empty).materialize = none := by decide +kernel
example : box.dropWork = (Slot.ofValue word).dropWork.plus (Slot.boxed .empty).dropWork :=
  box.take_work [.deref] (by simp [box, Slot.take, Slot.materialize_ofValue])

-- A shared referent can be read but neither moved out nor destroyed with the pointer.
private def shared : Slot := .shared word
example : shared.read [.deref] = some word := by simp [shared, Slot.read, Slot.get, Slot.materialize_ofValue]
example : shared.take [.deref] = none := by decide +kernel
example : shared.take [.deref, .field (some 1) 0] = none := by decide +kernel
example : shared.dropWork = ⟨1, 0⟩ := by decide +kernel

-- Partial local moves keep every other local, including an unrelated owner.
private def env : Partial.Locals := fun slot =>
  if slot = 3 then tuple else if slot = 8 then box else .empty
private def place : Place := .field (.local 3) none 0
private def after : Partial.Locals := env.set 3 rest
example : env.move place = some (word, after) := by
  have ht : tuple.take first = some (word, rest) := by simp [tuple, first, rest, Slot.take, Slot.materialize_ofValue]
  change (do let (value, remaining) ← tuple.take first
             some (value, env.set 3 remaining)) = some (word, after)
  rw [ht]
  rfl
example : after 8 = box := by simp [after, Partial.Locals.set, env]
example : after 3 = rest := by simp [after, Partial.Locals.set]
example : (after.drop 3).2 = ⟨2, 0⟩ := by decide +kernel
example : (after.drop 3).1 8 = box := by simp [Partial.Locals.drop, Partial.Locals.set, after, env]
example : ((after.drop 3).1.drop 3).2 = {} := after.drop_twice 3

-- Complete locals retain the old whole-local move interpretation.
example (old : Env) (slot : Nat) :
    (Partial.Locals.lift old).move (.local slot) =
      (evalOperand old (.move slot)).map (fun (value, final) => (value, Partial.Locals.lift final)) :=
  Partial.Locals.move_local_lift old slot

end SourcePartialTests
