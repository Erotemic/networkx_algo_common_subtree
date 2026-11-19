module

public import SubtreeProofs.Rust.LookupHeapExecution
public import SubtreeProofs.Rust.MemoSourceRefinement

/-! Actual addressed execution for the certified memo primitives. Instruction
execution and its simulation proof are shared with lookup; only the function
entry/Box driver is specialized to the memo helper set. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Heap

open LookupSource LookupSource.Heap

abbrev Calls := LookupSource.Heap.CallsFor Function

def run (body : Function → MemoSource.Code) : Nat → Calls
  | 0, _, _, _ => none
  | fuel + 1, function, args, memory =>
    if function = .boxNew then
      match args with
      | [value] => some ((alloc memory value).1, (alloc memory value).2, ⟨1, MemoSource.entryEvents function⟩)
      | _ => none
    else do
      let (outcome, memory, cost) ← LookupSource.Heap.exec (run body fuel) (body function) memory (initialLocals args)
      match outcome with
      | .next _ => none
      | .returned value => some (value, memory, (⟨1, MemoSource.entryEvents function⟩ : Cost).plus cost)

theorem run_spec (body : Function → Code) (hb : ∀ function, codeBorrows (body function) = true)
    (fuel : Nat) : CallsRefine (run body fuel) (MemoSource.run body fuel) := by
  induction fuel with
  | zero => intro function memory cells values value cost _ hr; cases hr
  | succ fuel ih =>
    intro function memory cells values value cost hargs hr
    rw [MemoSource.run_succ] at hr
    by_cases hf : function = .boxNew
    · subst function
      simp only [ite_true] at hr
      cases values with
      | nil => cases hr
      | cons head tail =>
        cases tail with
        | cons _ _ => cases hr
        | nil =>
          cases hr
          cases hargs with
          | cons hhead htail =>
            cases htail
            refine ⟨(alloc memory _).1, (alloc memory _).2, ?_, alloc_rep hhead,
              Extends.append memory [_], (alloc_fresh memory _).2.2⟩
            simp [run]
    · simp only [hf, ite_false] at hr
      cases hx : LookupSource.exec (MemoSource.run body fuel) (body function) (initialEnv values) with
      | none => simp [hx] at hr
      | some pair =>
        rcases pair with ⟨outcome, inner⟩
        simp only [hx, bind, Option.bind] at hr
        cases outcome with
        | next _ => cases hr
        | returned v =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨result, after, he, hv, hex, hlen⟩ :=
            exec_spec ih (body function) (hb function) (initial_rep hargs) hx
          cases result with
          | next _ => cases hv
          | returned cell =>
            refine ⟨cell, after, by simp [run, hf, he], hv, hex, ?_⟩
            have hz : (entryEvents function).allocations = 0 := by cases function <;> simp_all [entryEvents]
            simpa [Cost.plus, LookupEvents.Events.plus, hz] using hlen


theorem program_borrows (function : Function) : codeBorrows (Program.body function) = true := by
  cases function <;> decide +kernel

theorem certified_run_spec (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost)
    (hargs : RepresentsFields memory cells values)
    (hr : sourceRun Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, run Program.body fuel function cells memory = some (cell, after, cost) ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  rw [Certificate.original_run] at hr
  exact run_spec Program.body program_borrows fuel function memory cells values value cost hargs hr

end SubtreeProofs.Rust.MemoSource.Heap
