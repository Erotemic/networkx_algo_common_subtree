import SubtreeProofs.Rust.MemoBorrowRefinement

namespace MemoBorrowTests

open SubtreeProofs.Rust LookupSource LookupSource.Heap Borrow verified_ordered_core

private def base : Memory := [.node .word 0 []]
private def grown : Memory := base ++ [.node .word 0 []]
private theorem loan : Loan base ⟨0, []⟩ (.adt .word) := ⟨⟨_, rfl, .node .emptyWord .nil⟩⟩

-- Fresh validity alone does not supply a loan in the retained caller heap.
example : Typed grown (.shared ⟨1, []⟩) (.shared (.adt .word)) := .shared rfl (.node .emptyWord .nil)
example : ¬Loan base ⟨1, []⟩ (.adt .word) := by
  intro h
  have hb := h.root_bound
  change 1 < 1 at hb
  omega
example : ∃ cell, read grown ⟨0, []⟩ = some cell ∧ Typed grown cell (.adt .word) :=
  loan.stable (Extends.append base [_])

-- The limited shared-root profile is unchanged; a fresh-owned-root borrow
-- can be well typed and valid Rust while outside this retained-base profile.
private def freshBorrow : MemoSource.Code := .step (.call .boxNew [.boolean true] 0)
  (.step (.assign 1 (.address (.deref (.local 0)))) .done)
example : MemoSource.Types.checkCode [.owned .boolean, .shared .boolean] (.shared .boolean) freshBorrow = true := by decide +kernel
example : codeRoutes [.owned .boolean, .shared .boolean] freshBorrow = false := by decide +kernel
example : fromShared [.shared (.owned (.adt .word))] (.deref (.deref (.local 0))) = true := rfl

-- Generic Box preserves a loan in its payload; it is not an ordinary closed result.
example : ∃ cell after,
    MemoSource.Heap.run MemoSource.Program.body 1 .boxNew [.shared ⟨0, []⟩] base =
      some (cell, after, ⟨1, MemoSource.entryEvents .boxNew⟩) ∧
    Safe base after cell (.owned (.shared (.adt .word))) ∧
    MemoSource.Borrow.RunSafe base MemoSource.Program.body 1 .boxNew [.shared ⟨0, []⟩] base cell after
      ⟨1, MemoSource.entryEvents .boxNew⟩ := by
  have hr : MemoSource.Heap.run MemoSource.Program.body 1 .boxNew [.shared ⟨0, []⟩] base =
      some (.owned 1, base ++ [.shared ⟨0, []⟩], ⟨1, MemoSource.entryEvents .boxNew⟩) := rfl
  obtain ⟨hs, _, htrace⟩ := MemoSource.Borrow.original_safe base 1 .boxNew [.shared ⟨0, []⟩]
    [.shared (.adt .word)] base (.owned 1) (base ++ [.shared ⟨0, []⟩]) _ (.owned (.shared (.adt .word)))
    (.refl base) (.cons (.shared loan) .nil) rfl hr
  exact ⟨_, _, hr, hs, htrace⟩
example : ¬Unborrowed (base ++ [.shared ⟨0, []⟩]) (.owned 1) := by
  intro h
  cases h with
  | owned hr child => cases hr; cases child

private def word : Cell := .node .word 0 []
private def witness : CommonEmbedding := ⟨.Empty, 77#u32⟩
private def entry : Cell := .node .entry 0 [word, word, .node .embedding 0 [word, .number 77]]
private def memory : Memory := [entry, .node .table 0 [], .number 12]
private def table : Cell := .node .table 1 [.owned 0, .owned 1]
private def native : MemoTable := .Entry ⟨.Empty, .Empty, witness⟩ .Empty

private theorem table_rep : Represents memory table (encodeTable native) :=
  .node (.cons (.owned rfl (.node (.cons (.node .nil) (.cons (.node .nil)
    (.cons (.node (.cons (.node .nil) (.cons (.number 77) .nil))) .nil)))))
    (.cons (.owned rfl (.node .nil)) .nil))
private theorem key_rep : Represents memory (.shared ⟨0, [0]⟩) (.reference (encodeWord .Empty)) := .shared rfl (.node .nil)
private theorem result_rep : Represents memory (.shared ⟨0, [2]⟩) (.reference (encodeResult witness)) :=
  .shared rfl (.node (.cons (.node .nil) (.cons (.number 77) .nil)))

-- Query and result pointers borrow into the table consumed by insertion.
-- Their exact typed targets survive, as does an unrelated caller loan.
example : ∃ cell after cost,
    MemoSource.Heap.run MemoSource.Program.body 4 .insert
      [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory = some (cell, after, cost) ∧
    MemoSource.Borrow.RunSafe memory MemoSource.Program.body 4 .insert
      [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory cell after cost ∧
    Unborrowed after cell ∧
    (∃ target, read after ⟨0, [0]⟩ = some target ∧ Typed after target (.adt .word)) ∧
    (∃ target, read after ⟨2, []⟩ = some target ∧ Typed after target .u32) := by
  obtain ⟨cell, after, cost, _, hr, htrace, _, hclosed, _⟩ :=
    MemoSource.Borrow.insert_loan_total native .Empty .Empty witness 4 (by decide +kernel)
      memory table ⟨0, [0]⟩ ⟨0, [0]⟩ ⟨0, [2]⟩ table_rep key_rep key_rep result_rep
  have hargs : FieldsTyped memory [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩]
      (MemoSource.Types.inputs .insert) :=
    .cons (table_rep.typed (table_typed native)) (.cons (key_rep.typed (.shared (word_typed .Empty)))
      (.cons (key_rep.typed (.shared (word_typed .Empty))) (.cons (result_rep.typed (.shared (result_typed witness))) .nil)))
  have hex := (MemoSource.Borrow.ordinary_loans 4 .insert (by decide) memory _ hargs hr).2.2.2
  have keyLoan : Loan memory ⟨0, [0]⟩ (.adt .word) := ⟨⟨word, rfl, .node .emptyWord .nil⟩⟩
  have otherLoan : Loan memory ⟨2, []⟩ .u32 := ⟨⟨.number 12, rfl, .number (by decide)⟩⟩
  exact ⟨cell, after, cost, hr, htrace, hclosed, keyLoan.stable hex, otherLoan.stable hex⟩

end MemoBorrowTests
