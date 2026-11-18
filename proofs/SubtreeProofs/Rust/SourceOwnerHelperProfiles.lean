module

public import SubtreeProofs.Rust.SourceOwnerHelperResults

/-! Independent source types and actual readable cells derive the existing
helper ownership profiles. False flags require plain values; the insertion's
owned table remains a potentially owning value. Shared reads may alias. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

theorem Typed.plain_input {memory : Memory} {cell : Cell} {ty : Ty} (h : Typed memory cell ty)
    (plain : ty = .boolean ∨ ty = .u32 ∨ ∃ inner, ty = .shared inner) : Frame.Plain cell := by
  rcases plain with rfl | rfl | ⟨inner, rfl⟩ <;> cases h <;> first | (cases_type Shape) | constructor

theorem FieldsTyped.length {memory : Memory} {cells : List Cell} {types : List Ty}
    (h : FieldsTyped memory cells types) : cells.length = types.length := by
  induction cells generalizing types with
  | nil => cases h; rfl
  | cons cell cells ih => cases h with
    | cons first rest => exact congrArg Nat.succ (ih rest)

theorem FieldsTyped.plain_inputs {memory : Memory} {cells : List Cell} {types : List Ty}
    (h : FieldsTyped memory cells types)
    (plain : ∀ ty ∈ types, ty = .boolean ∨ ty = .u32 ∨ ∃ inner, ty = .shared inner) : Frame.PlainFields cells := by
  induction cells generalizing types with
  | nil => cases h; exact .nil
  | cons cell cells ih => cases h with
    | cons first rest =>
      exact .cons (first.plain_input (plain _ (by simp))) (ih rest (fun ty hm => plain ty (List.mem_cons_of_mem _ hm)))

theorem lookup_typed_profile {memory : Memory} {cells : List Cell} (function : LookupSource.Function)
    (hf : function ≠ .boxNew) (h : FieldsTyped memory cells (SourceTypes.inputs function)) : Frame.ArgsMatch function cells := by
  have plain := h.plain_inputs (by
    intro ty hm
    cases function <;> simp_all [SourceTypes.inputs]
    rcases hm with rfl | rfl <;> exact Or.inr (Or.inr ⟨_, rfl⟩))
  have length : cells.length = Frame.arity function := h.length.trans (by cases function <;> simp_all [SourceTypes.inputs, Frame.arity])
  exact ⟨length, Or.inr (by simpa only [Frame.inputFlags, ← length] using plain.matches)⟩

end SubtreeProofs.Rust.LookupSource.Heap

namespace SubtreeProofs.Rust.MemoSource.Heap

open LookupSource LookupSource.Heap

theorem typed_profile {memory : Memory} {cells : List Cell} (function : MemoSource.Function)
    (hf : function ≠ .boxNew) (h : FieldsTyped memory cells (Types.inputs function)) : Frame.ArgsMatch function cells := by
  by_cases hi : function = .insert
  · subst function
    cases h with
    | @cons cell ty cells types table rest =>
      have plain := rest.plain_inputs (by
        intro ty hm
        simp_all
        rcases hm with rfl | rfl <;> exact Or.inr (Or.inr ⟨_, rfl⟩))
      have hm : LookupSource.Heap.Frame.FieldsMatch [false, false, false] cells := by
        simpa [rest.length] using plain.matches
      exact ⟨by simp only [List.length_cons, rest.length]; rfl, Or.inr ⟨trivial, hm⟩⟩
  · have plain := h.plain_inputs (by
      intro ty hm
      cases function <;> simp_all [Types.inputs])
    have length : cells.length = MemoSource.arity function := h.length.trans (by cases function <;> simp_all [Types.inputs, MemoSource.arity])
    refine ⟨length, Or.inr ?_⟩
    have flags : Frame.inputFlags function = List.replicate cells.length false := by
      rw [length]
      cases function <;> simp_all [Frame.inputFlags, MemoSource.arity]
    rw [flags]
    exact plain.matches

end SubtreeProofs.Rust.MemoSource.Heap

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap Partial Partial.Addressed Storage

theorem typed_lookup_profile {world : World} (function : LookupSource.Function) (hf : function ≠ .boxNew)
    {packets : List ValueCell} (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world (SourceEval.Helpers.lookupFunction function) packets) :
    Heap.Frame.ArgsMatch function (packets.map Prod.fst) := by
  obtain ⟨types, ty, typed, output⟩ := ht
  have different : SourceEval.Helpers.lookupFunction function ≠ .boxNew := by cases function <;> simp_all [SourceEval.Helpers.lookupFunction]
  have he := (Types.callOutput_standard different output).1
  rw [he] at typed
  have input : Types.inputs (SourceEval.Helpers.lookupFunction function) = SourceTypes.inputs function := by
    cases function <;> rfl
  rw [input] at typed
  exact Heap.lookup_typed_profile function hf ((packets_represented hp).typed typed)

theorem typed_memo_profile {world : World} (function : MemoSource.Function) (hf : function ≠ .boxNew)
    {packets : List ValueCell} (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world (SourceEval.Helpers.memoFunction function) packets) :
    MemoSource.Frame.ArgsMatch function (packets.map Prod.fst) := by
  obtain ⟨types, ty, typed, output⟩ := ht
  have different : SourceEval.Helpers.memoFunction function ≠ .boxNew := by cases function <;> simp_all [SourceEval.Helpers.memoFunction]
  have he := (Types.callOutput_standard different output).1
  rw [he] at typed
  have input : Types.inputs (SourceEval.Helpers.memoFunction function) = MemoSource.Types.inputs function := by
    cases function <;> rfl
  rw [input] at typed
  exact MemoSource.Heap.typed_profile function hf ((packets_represented hp).typed typed)

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
