module

public import SubtreeProofs.Rust.LookupStackExecution
public import SubtreeProofs.Rust.MemoHeapExecution

/-! Recursive local-storage safety for a checked stack program. Each call has
its own allocation/initialization state; successful recursive calls are proved
safe by fuel induction. This does not model physical stack addresses. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Stack

open LookupSource LookupSource.Heap LookupSource.Stack

abbrev Code := LookupSource.Stack.Code Function
abbrev CallSafety := LookupSource.Heap.Frame.CallSafetyFor Function
abbrev CallSound := LookupSource.Stack.CallSoundWith arity
abbrev Trace := LookupSource.Stack.TraceWith arity


def erased (body : Function → Code) : Function → MemoSource.Code := fun function => (body function).erase

def RunSafe (body : Function → Code) (count : Function → Nat) : Nat → CallSafety
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    if function = .boxNew then MemoSource.Heap.run (erased body) (fuel + 1) function cells memory = some (cell, after, cost)
    else ∃ inner,
      Trace (MemoSource.Heap.run (erased body) fuel) (RunSafe body count fuel) (body function)
        (initial (count function) (arity function)) memory (initialLocals cells) (.returned cell) after inner ∧
      cost = (⟨1, entryEvents function⟩ : Cost).plus inner

def BodyChecked (body : Function → Code) (count : Function → Nat) : Prop :=
  ∀ function, function ≠ .boxNew →
    verifyWith arity (body function) (initial (count function) (arity function)) (fun _ => false) = true

theorem RunSafe.erases (body : Function → Code) (count : Function → Nat) (fuel : Nat)
    {function : Function} {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunSafe body count fuel function cells memory cell after cost) :
    MemoSource.Heap.run (erased body) fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    by_cases hf : function = .boxNew
    · simpa [RunSafe, hf] using h
    · simp only [RunSafe, hf, ite_false] at h
      obtain ⟨inner, trace, rfl⟩ := h
      simp only [MemoSource.Heap.run, hf, ite_false, erased, trace.erases, bind, Option.bind]

theorem run_sound (body : Function → Code) (count : Function → Nat) (hb : BodyChecked body count)
    (fuel : Nat) : CallSound (MemoSource.Heap.run (erased body) fuel) (RunSafe body count fuel) := by
  induction fuel with
  | zero => intro function cells memory cell after cost _ hr; cases hr
  | succ fuel ih =>
    intro function cells memory cell after cost hargs hr
    by_cases hf : function = .boxNew
    · simpa [RunSafe, hf] using hr
    · have he : StateRep (initial (count function) (arity function)) (initialLocals cells) := by
        rw [← hargs]
        exact initial_rep _ _
      simp only [MemoSource.Heap.run, hf, ite_false] at hr
      cases hx : LookupSource.Heap.exec (MemoSource.Heap.run (erased body) fuel) (erased body function) memory (initialLocals cells) with
      | none => simp [hx] at hr
      | some pair =>
        rcases pair with ⟨outcome, mem, inner⟩
        simp only [hx, bind, Option.bind] at hr
        cases outcome with
        | next _ => cases hr
        | returned value =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          have trace := (verify_soundWith ih (body function) (fun _ => false) (hb function hf) he hx).1
          simp only [RunSafe, hf, ite_false]
          exact ⟨inner, trace, rfl⟩

end SubtreeProofs.Rust.MemoSource.Stack
