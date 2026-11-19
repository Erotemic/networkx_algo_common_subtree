import SubtreeProofs.Rust.LookupBorrowRefinement

namespace LookupBorrowTests

open SubtreeProofs.Rust.LookupSource Heap Borrow

private def base : Memory := [.node .word 0 []]
private def current : Memory := base ++ [.node .word 0 []]
private theorem loan : Loan base ⟨0, []⟩ (.adt .word) := ⟨⟨_, rfl, .node .emptyWord .nil⟩⟩

-- An existing loan survives allocation; its exact earlier target is retained.
example : ∃ cell, read current ⟨0, []⟩ = some cell ∧ Typed current cell (.adt .word) :=
  loan.stable (Extends.append base [_])

-- A currently valid pointer into a new allocation has no loan in the old heap.
example : Typed current (.shared ⟨1, []⟩) (.shared (.adt .word)) := .shared rfl (.node .emptyWord .nil)
example : ¬ Loan base ⟨1, []⟩ (.adt .word) := by
  intro h
  have hb := h.root_bound
  change 1 < 1 at hb
  omega

-- A local containing a fresh Box cannot mint an old-heap shared loan.
example : fromShared [.owned (.adt .word)] (.deref (.local 0)) = false := rfl
example : fromShared [.shared (.owned (.adt .word))] (.deref (.deref (.local 0))) = true := rfl
example : fromShared [.shared (.adt .word)] (.local 0) = false := rfl

-- Borrowing a fresh Box can be type-correct while outside the old-root profile.
-- This fragment is not asserted to be an invalid Rust borrow.
private def freshBorrow : Code := .step (.call .boxNew [.boolean true] 0)
  (.step (.assign 1 (.address (.deref (.local 0)))) .done)
example : SourceTypes.checkCode [.owned .boolean, .shared .boolean] (.shared .boolean) freshBorrow = true := by
  decide +kernel
example : codeRoutes [.owned .boolean, .shared .boolean] freshBorrow = false := by decide +kernel

-- Dropping the local shared-pointer slot does not destroy its heap referent.
private def env : Locals := fun index => if index = 0 then some (.shared ⟨0, []⟩) else none
example : borrow base env (.deref (.local 0)) = some (.shared ⟨0, []⟩) := rfl
example : read base ⟨0, []⟩ = some (.node .word 0 []) := rfl
example : (env.set 0 none) 0 = none := rfl
example : Loan base ⟨0, []⟩ (.adt .word) := loan

-- Mutation/freeing violate the extension premise rather than preserving loans.
example : ¬ Extends base [] := by
  intro h
  have hc := h 0 (.node .word 0 []) rfl
  cases hc
example : ¬ Extends base [.boolean true] := by
  intro h
  have hc := h 0 (.node .word 0 []) rfl
  cases hc

-- References hidden in a Box also prevent a result from being borrow-free.
private def boxedLoan : Memory := base ++ [.shared ⟨0, []⟩]
example : Safe base boxedLoan (.owned 1) (.owned (.shared (.adt .word))) := .owned rfl (.shared loan)
example : Typed boxedLoan (.owned 1) (.owned (.shared (.adt .word))) :=
  .owned rfl (.shared rfl (.node .emptyWord .nil))
example : ¬ Unborrowed boxedLoan (.owned 1) := by
  intro h
  cases h with
  | owned hr hchild =>
    cases hr
    cases hchild

example {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body 3 .lookup [.shared ⟨0, []⟩, .shared ⟨1, []⟩, .shared ⟨1, []⟩]
      [.node .table 0 [], .node .word 0 []] = some (cell, after, cost)) : Unborrowed after cell :=
  (lookup_loans 3 _ _ _ _ (.shared rfl (.node .emptyTable .nil))
    (.shared rfl (.node .emptyWord .nil)) (.shared rfl (.node .emptyWord .nil)) hr).2.2.1

end LookupBorrowTests
