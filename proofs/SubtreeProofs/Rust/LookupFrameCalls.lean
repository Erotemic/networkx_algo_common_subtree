module

public import SubtreeProofs.Rust.LookupFrameExecution
public import SubtreeProofs.Rust.LookupSourceMutation

/-! Recursive frame safety for the actual generated call graph. Callee
contracts are discharged by fuel induction; no assumed whole-program safety
field or final returned-ownership argument is used. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Frame

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def RunSafe (body : Function → Code) : Nat → CallSafety
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    if function = .boxNew then
      Heap.run body (fuel + 1) function cells memory = some (cell, after, cost)
    else
      ∃ inner,
        Guarded (Heap.run body fuel) (RunSafe body fuel) (body function) memory
          (initialLocals cells) (.returned cell) after inner ∧
        cost = (⟨1, entryEvents function⟩ : Cost).plus inner

def BodyChecked (body : Function → Code) (padding : Nat) : Prop :=
  ∀ function, function ≠ .boxNew →
    verify (body function) (initialState padding (inputFlags function))
      (outputFlag function) (fun _ => false) = true

theorem RunSafe.erases (body : Function → Code) (fuel : Nat) {function : Function}
    {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunSafe body fuel function cells memory cell after cost) :
    Heap.run body fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    by_cases hf : function = .boxNew
    · simpa [RunSafe, hf] using h
    · simp only [RunSafe, hf, ite_false] at h
      obtain ⟨inner, hg, rfl⟩ := h
      simp only [Heap.run, hf, ite_false, hg.erases, bind, Option.bind]

theorem run_sound (body : Function → Code) (padding : Nat) (hb : BodyChecked body padding)
    (fuel : Nat) : CallSound (Heap.run body fuel) (RunSafe body fuel) := by
  induction fuel with
  | zero => intro function cells memory cell after cost _ hr; cases hr
  | succ fuel ih =>
    intro function cells memory cell after cost hargs hr
    by_cases hf : function = .boxNew
    · subst function
      exact ⟨by trivial, by simpa [RunSafe] using hr⟩
    · have hi : FieldsMatch (inputFlags function) cells := by
        rcases hargs.2 with hf' | hi
        · exact False.elim (hf hf')
        · exact hi
      have he := initial_rep padding hi
      simp only [Heap.run, hf, ite_false] at hr
      cases hx : Heap.exec (Heap.run body fuel) (body function) memory (initialLocals cells) with
      | none => simp [hx] at hr
      | some pair =>
        rcases pair with ⟨outcome, mem, inner⟩
        simp only [hx, bind, Option.bind] at hr
        cases outcome with
        | next _ => cases hr
        | returned value =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          obtain ⟨hg, hp⟩ := verify_sound ih (body function) (fun _ => false)
            (outputFlag function) (hb function hf) he hx
          refine ⟨hp, ?_⟩
          simp only [RunSafe, hf, ite_false]
          exact ⟨inner, hg, rfl⟩

theorem original_checked : BodyChecked Program.body 20 := by
  intro function hf
  cases function <;> first | contradiction | decide +kernel

theorem mutant_checked : BodyChecked ExtraCompare.body 20 := by
  intro function hf
  cases function <;> first | contradiction | decide +kernel

theorem original_run_safe (fuel : Nat) (function : Function) (cells : List Cell) (memory : Memory)
    {cell : Cell} {after : Memory} {cost : Cost} (hargs : ArgsMatch function cells)
    (hr : Heap.run Program.body fuel function cells memory = some (cell, after, cost)) :
    RunSafe Program.body fuel function cells memory cell after cost :=
  (run_sound Program.body 20 original_checked fuel function cells memory cell after cost hargs hr).2

theorem mutant_run_safe (fuel : Nat) (function : Function) (cells : List Cell) (memory : Memory)
    {cell : Cell} {after : Memory} {cost : Cost} (hargs : ArgsMatch function cells)
    (hr : Heap.run ExtraCompare.body fuel function cells memory = some (cell, after, cost)) :
    RunSafe ExtraCompare.body fuel function cells memory cell after cost :=
  (run_sound ExtraCompare.body 20 mutant_checked fuel function cells memory cell after cost hargs hr).2

end SubtreeProofs.Rust.LookupSource.Heap.Frame
