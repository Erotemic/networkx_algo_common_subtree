module

public import SubtreeProofs.Rust.SourcePartialTyping

/-! Type preservation of partial-local reads, moves, stores and clears.
Only declared slots are constrained; static source bounds separately exclude
out-of-range accesses. These lemmas do not assert initialization or loan validity. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial

open Heap SourceTypes

theorem inferPath_append (ty : Ty) (path suffix : List Projection) :
    inferPath ty (path ++ suffix) = (do inferPath (← inferPath ty path) suffix) := by
  induction path generalizing ty with
  | nil => simp only [inferPath, List.nil_append, bind, Option.bind]
  | cons projection rest ih =>
    cases projection <;> simp only [List.cons_append, inferPath, ih, bind, Option.bind_assoc]

theorem inferPlace_split (locals : List Ty) (place : Place) :
    inferPlace locals place = (do inferPath (← locals[(splitPlace place).1]?) (splitPlace place).2) := by
  induction place with
  | «local» slot =>
    simp only [inferPlace, splitPlace, inferPath]
    cases locals[slot]? <;> rfl
  | deref parent ih =>
    simp only [inferPlace, ih, splitPlace, inferPath_append]
    cases hs : splitPlace parent with
    | mk slot path =>
      cases hl : locals[slot]? with
      | none => rfl
      | some ty =>
        cases hp : inferPath ty path with
        | none => simp only [bind, Option.bind, hp]
        | some inner => simp only [bind, Option.bind, hp, inferPath]; cases deref inner <;> rfl
  | field parent variant index ih =>
    simp only [inferPlace, ih, splitPlace, inferPath_append]
    cases hs : splitPlace parent with
    | mk slot path =>
      cases hl : locals[slot]? with
      | none => rfl
      | some ty =>
        cases hp : inferPath ty path with
        | none => simp only [bind, Option.bind, hp]
        | some inner => simp only [bind, Option.bind, hp, inferPath]; cases fieldType inner variant index <;> rfl

theorem inferPlace_root {locals : List Ty} {place : Place} {ty : Ty}
    (h : inferPlace locals place = some ty) :
    ∃ root, locals[(splitPlace place).1]? = some root ∧ inferPath root (splitPlace place).2 = some ty := by
  rw [inferPlace_split] at h
  cases hl : locals[(splitPlace place).1]? with
  | none => simp [hl] at h
  | some root => exact ⟨root, rfl, by simpa only [hl, bind, Option.bind] using h⟩

def LocalsTyped (locals : List Ty) (state : Locals) : Prop :=
  ∀ slot ty, locals[slot]? = some ty → SlotTyped (state slot) ty

theorem LocalsTyped.clear {locals : List Ty} {state : Locals}
    (h : LocalsTyped locals state) (slot : Nat) : LocalsTyped locals (state.set slot .empty) := by
  intro index ty ht
  by_cases hi : index = slot
  · subst index
    simpa only [Locals.set, ite_true] using SlotTyped.empty ty
  · simpa only [Locals.set, hi, ite_false] using h index ty ht

theorem LocalsTyped.store {locals : List Ty} {state : Locals} (h : LocalsTyped locals state)
    {slot : Nat} {part : Slot} {ty : Ty} (ht : locals[slot]? = some ty) (hv : SlotTyped part ty) :
    LocalsTyped locals (state.set slot part) := by
  intro index target hi
  by_cases he : index = slot
  · subst index
    rw [ht] at hi
    cases hi
    simpa only [Locals.set, ite_true] using hv
  · simpa only [Locals.set, he, ite_false] using h index target hi

theorem LocalsTyped.read {locals : List Ty} {state : Locals} (h : LocalsTyped locals state)
    {place : Place} {ty : Ty} {value : Value} (ht : inferPlace locals place = some ty)
    (hr : state.read place = some value) : SnapshotTyped value ty := by
  obtain ⟨root, hl, hp⟩ := inferPlace_root ht
  exact (h _ root hl).read _ hp hr

theorem LocalsTyped.move {locals : List Ty} {state after : Locals} (h : LocalsTyped locals state)
    {place : Place} {ty : Ty} {value : Value} (ht : inferPlace locals place = some ty)
    (hr : state.move place = some (value, after)) : SnapshotTyped value ty ∧ LocalsTyped locals after := by
  obtain ⟨root, hl, hp⟩ := inferPlace_root ht
  rcases hs : splitPlace place with ⟨slot, path⟩
  simp only [hs] at hl hp
  simp only [Locals.move, hs] at hr
  cases hm : (state slot).take path with
  | none => simp [hm] at hr
  | some pair =>
    rcases pair with ⟨moved, remaining⟩
    simp only [hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hh := (h slot root hl).take path hp hm
    exact ⟨hh.1, h.store hl hh.2⟩

end SubtreeProofs.Rust.LookupSource.Partial
