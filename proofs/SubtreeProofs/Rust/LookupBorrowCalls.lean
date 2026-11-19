module

public import SubtreeProofs.Rust.LookupBorrowExecution
public import SubtreeProofs.Rust.LookupBorrowCertificate

/-! Recursive discharge of typed shared-loan contracts. The retained base
heap is fixed across all nested helper calls. New Box payloads preserve their
existing loans; source-certified reborrows introduce only loans into the base. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

theorem fieldsSafe_slot {base current : Memory} {cells : List Cell} {types : List Ty}
    (h : FieldsSafe base current cells types) (index : Nat) {cell : Cell}
    (hc : cells[index]? = some cell) : ∃ ty, types[index]? = some ty ∧ Safe base current cell ty := by
  induction index generalizing cells types with
  | zero => cases h with
    | nil => cases hc
    | cons first rest => cases hc; exact ⟨_, rfl, first⟩
  | succ index ih => cases h with
    | nil => cases hc
    | cons first rest => exact ih rest hc

theorem initial_safe {base current : Memory} {cells : List Cell} {types locals : List Ty} {output : Ty}
    (hargs : FieldsSafe base current cells types) (hb : locals.take (types.length + 1) = output :: types) :
    EnvSafe base current locals (initialLocals cells) := by
  intro slot cell hc
  by_cases hzero : slot = 0
  · simp [initialLocals, hzero] at hc
  · simp only [initialLocals, hzero, ite_false] at hc
    obtain ⟨ty, ht, hv⟩ := fieldsSafe_slot hargs (slot - 1) hc
    have hi : slot - 1 < types.length := List.getElem?_eq_some_iff.mp ht |>.choose
    have hs : slot = (slot - 1) + 1 := by omega
    have hl : locals[slot]? = (output :: types)[slot]? := by
      rw [← hb]
      exact (List.getElem?_take_of_lt (by omega)).symm
    rw [hs, List.getElem?_cons_succ, ht] at hl
    exact ⟨ty, by simpa only [← hs] using hl, hv⟩

theorem alloc_safe {base current : Memory} {cell : Cell} {ty : Ty} (h : Safe base current cell ty) :
    Safe base (alloc current cell).2 (alloc current cell).1 (.owned ty) :=
  .owned (alloc_fresh current cell).2.1 (h.mono (Extends.append current [cell]))

def RunSafe (base : Memory) (body : Function → LookupSource.Code) : Nat → Frame.CallSafety
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    if function = .boxNew then Heap.run body (fuel + 1) function cells memory = some (cell, after, cost)
    else ∃ locals inner,
      Trace base (Heap.run body fuel) (RunSafe base body fuel) locals (SourceTypes.output function)
        (body function) memory (initialLocals cells) (.returned cell) after inner ∧
      cost = (⟨1, entryEvents function⟩ : Cost).plus inner

theorem RunSafe.erases (base : Memory) (body : Function → LookupSource.Code) (fuel : Nat)
    {function : Function} {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunSafe base body fuel function cells memory cell after cost) :
    Heap.run body fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    by_cases hf : function = .boxNew
    · simpa [RunSafe, hf] using h
    · simp only [RunSafe, hf, ite_false] at h
      obtain ⟨locals, inner, trace, rfl⟩ := h
      simp only [Heap.run, hf, ite_false, trace.erases, bind, Option.bind]

theorem run_safe (base : Memory) (body : Function → LookupSource.Code) (hb : BodiesChecked body) (fuel : Nat) :
    CallsSafe base (Heap.run body fuel) (RunSafe base body fuel) := by
  induction fuel with
  | zero => intro function cells types memory cell after cost ty _ _ _ hr; cases hr
  | succ fuel ih =>
    intro function cells types memory cell after cost ty hext hargs ht hr
    by_cases hf : function = .boxNew
    · subst function
      have hraw := hr
      simp only [SourceTypes.callOutput, ite_true] at ht
      cases types with
      | nil => cases ht
      | cons inner rest => cases rest with
        | cons _ _ => cases ht
        | nil =>
          cases ht
          cases hargs with
          | cons hvalue htail =>
            cases htail
            simp only [Heap.run, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨alloc_safe hvalue, Extends.append memory [_], by simpa [RunSafe] using hraw⟩
    · simp only [SourceTypes.callOutput, hf, ite_false] at ht
      split at ht
      next heq =>
        have heq := SourceTypes.sameList_eq heq
        subst types
        cases ht
        obtain ⟨locals, hprefix, hcode, hroutes⟩ := hb function hf
        simp only [Heap.run, hf, ite_false] at hr
        cases hx : Heap.exec (Heap.run body fuel) (body function) memory (initialLocals cells) with
        | none => simp [hx] at hr
        | some pair =>
          rcases pair with ⟨result, mem, inner⟩
          simp only [hx, bind, Option.bind] at hr
          cases result with
          | next _ => cases hr
          | returned value =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            obtain ⟨trace, hp, hex⟩ := exec_safe ih (body function) hext (initial_safe hargs hprefix) hcode hroutes hx
            refine ⟨hp, hex, ?_⟩
            simp only [RunSafe, hf, ite_false]
            exact ⟨locals, inner, trace, rfl⟩
      next => cases ht

theorem original_safe (base : Memory) (fuel : Nat) :
    CallsSafe base (Heap.run Program.body fuel) (RunSafe base Program.body fuel) :=
  run_safe base Program.body original_bodies fuel

theorem mutant_safe (base : Memory) (fuel : Nat) :
    CallsSafe base (Heap.run ExtraCompare.body fuel) (RunSafe base ExtraCompare.body fuel) :=
  run_safe base ExtraCompare.body mutant_bodies fuel

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
