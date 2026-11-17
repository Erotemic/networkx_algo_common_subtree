module

public import SubtreeProofs.Rust.LookupBorrowExecution
public import SubtreeProofs.Rust.LookupBorrowCalls
public import SubtreeProofs.Rust.MemoBorrowCertificate
public import SubtreeProofs.Rust.MemoHeapExecution

/-! Recursive discharge of typed shared-loan contracts. The retained base
heap is fixed across all nested helper calls. New Box payloads preserve their
existing loans; source-certified reborrows introduce only loans into the base. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Borrow

open LookupSource LookupSource.Heap LookupSource.Heap.Borrow

def RunSafe (base : Memory) (body : Function → MemoSource.Code) : Nat → LookupSource.Heap.Frame.CallSafetyFor Function
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    if function = .boxNew then MemoSource.Heap.run body (fuel + 1) function cells memory = some (cell, after, cost)
    else ∃ locals inner,
      Trace base (MemoSource.Heap.run body fuel) (RunSafe base body fuel) locals (Types.output function)
        (body function) memory (initialLocals cells) (.returned cell) after inner ∧
      cost = (⟨1, entryEvents function⟩ : Cost).plus inner

theorem RunSafe.erases (base : Memory) (body : Function → MemoSource.Code) (fuel : Nat)
    {function : Function} {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunSafe base body fuel function cells memory cell after cost) :
    MemoSource.Heap.run body fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    by_cases hf : function = .boxNew
    · simpa [RunSafe, hf] using h
    · simp only [RunSafe, hf, ite_false] at h
      obtain ⟨locals, inner, trace, rfl⟩ := h
      simp only [MemoSource.Heap.run, hf, ite_false, trace.erases, bind, Option.bind]

theorem run_safe (base : Memory) (body : Function → MemoSource.Code) (hb : BodiesChecked body) (fuel : Nat) :
    CallsSafeWith Types.callOutput base (MemoSource.Heap.run body fuel) (RunSafe base body fuel) := by
  induction fuel with
  | zero => intro function cells types memory cell after cost ty _ _ _ hr; cases hr
  | succ fuel ih =>
    intro function cells types memory cell after cost ty hext hargs ht hr
    by_cases hf : function = .boxNew
    · subst function
      have hraw := hr
      simp only [Types.callOutput, ite_true] at ht
      cases types with
      | nil => cases ht
      | cons inner rest => cases rest with
        | cons _ _ => cases ht
        | nil =>
          cases ht
          cases hargs with
          | cons hvalue htail =>
            cases htail
            simp only [MemoSource.Heap.run, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨alloc_safe hvalue, Extends.append memory [_], by simpa [RunSafe] using hraw⟩
    · simp only [Types.callOutput, hf, ite_false] at ht
      split at ht
      next heq =>
        have heq := SourceTypes.sameList_eq heq
        subst types
        cases ht
        obtain ⟨locals, hprefix, hcode, hroutes⟩ := hb function hf
        simp only [MemoSource.Heap.run, hf, ite_false] at hr
        cases hx : LookupSource.Heap.exec (MemoSource.Heap.run body fuel) (body function) memory (initialLocals cells) with
        | none => simp [hx] at hr
        | some pair =>
          rcases pair with ⟨result, mem, inner⟩
          simp only [hx, bind, Option.bind] at hr
          cases result with
          | next _ => cases hr
          | returned value =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            obtain ⟨trace, hp, hex⟩ := exec_safeWith ih (body function) hext (initial_safe hargs hprefix) hcode hroutes hx
            refine ⟨hp, hex, ?_⟩
            simp only [RunSafe, hf, ite_false]
            exact ⟨locals, inner, trace, rfl⟩
      next => cases ht

theorem original_safe (base : Memory) (fuel : Nat) :
    CallsSafeWith Types.callOutput base (MemoSource.Heap.run Program.body fuel) (RunSafe base Program.body fuel) :=
  run_safe base Program.body original_bodies fuel

end SubtreeProofs.Rust.MemoSource.Borrow
