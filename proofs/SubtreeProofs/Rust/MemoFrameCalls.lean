module

public import SubtreeProofs.Rust.MemoFrameProfile
public import SubtreeProofs.Rust.LookupFrameExecution
public import SubtreeProofs.Rust.MemoHeapExecution

/-! Actual recursive guarded local traces for memo helpers. The owned table
input is tracked until moved into its tail Box; all nonreturn locals are
empty or non-owning at return. Complete source costs are unchanged. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Frame

open LookupSource LookupSource.Heap LookupSource.Heap.Frame

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def RunSafe (body : Function → Code) : Nat → CallSafetyFor Function
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    if function = .boxNew then
      MemoSource.Heap.run body (fuel + 1) function cells memory = some (cell, after, cost)
    else
      ∃ inner,
        GuardedWith ArgsMatch (MemoSource.Heap.run body fuel) (RunSafe body fuel) (body function) memory
          (initialLocals cells) (.returned cell) after inner ∧
        cost = (⟨1, entryEvents function⟩ : Cost).plus inner

def BodyChecked (body : Function → Code) (padding : Nat) : Prop :=
  ∀ function, function ≠ .boxNew →
    verifyWith callProfile outputFlag (body function) (initialState padding (inputFlags function))
      (outputFlag function) (fun _ => false) = true

theorem RunSafe.erases (body : Function → Code) (fuel : Nat) {function : Function}
    {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunSafe body fuel function cells memory cell after cost) :
    MemoSource.Heap.run body fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    by_cases hf : function = .boxNew
    · simpa [RunSafe, hf] using h
    · simp only [RunSafe, hf, ite_false] at h
      obtain ⟨inner, hg, rfl⟩ := h
      simp only [MemoSource.Heap.run, hf, ite_false, hg.erases, bind, Option.bind]

theorem run_sound (body : Function → Code) (padding : Nat) (hb : BodyChecked body padding)
    (fuel : Nat) : CallSoundWith ArgsMatch outputFlag (MemoSource.Heap.run body fuel) (RunSafe body fuel) := by
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
      simp only [MemoSource.Heap.run, hf, ite_false] at hr
      cases hx : LookupSource.Heap.exec (MemoSource.Heap.run body fuel) (body function) memory (initialLocals cells) with
      | none => simp [hx] at hr
      | some pair =>
        rcases pair with ⟨outcome, mem, inner⟩
        simp only [hx, bind, Option.bind] at hr
        cases outcome with
        | next _ => cases hr
        | returned value =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          obtain ⟨hg, hp⟩ := verify_soundWith (profile := callProfile) (resultFlag := outputFlag) (argsMatch := ArgsMatch)
            (fun function _ _ hm hc => profile_sound (function := function) hm hc) ih (body function) (fun _ => false)
            (outputFlag function) (hb function hf) he hx
          refine ⟨hp, ?_⟩
          simp only [RunSafe, hf, ite_false]
          exact ⟨inner, hg, rfl⟩

theorem original_checked : BodyChecked Program.body 15 := by
  intro function hf
  cases function <;> first | contradiction | decide +kernel

theorem original_run_safe (fuel : Nat) (function : Function) (cells : List Cell) (memory : Memory)
    {cell : Cell} {after : Memory} {cost : Cost} (hargs : ArgsMatch function cells)
    (hr : MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost)) :
    RunSafe Program.body fuel function cells memory cell after cost :=
  (run_sound Program.body 15 original_checked fuel function cells memory cell after cost hargs hr).2

end SubtreeProofs.Rust.MemoSource.Frame
