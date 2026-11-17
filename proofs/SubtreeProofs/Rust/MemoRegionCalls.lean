module

public import SubtreeProofs.Rust.MemoRegionCertificate
public import SubtreeProofs.Rust.LookupRegionCalls
public import SubtreeProofs.Rust.LookupRegionSemantics
public import SubtreeProofs.Rust.LookupBorrowExecution
public import SubtreeProofs.Rust.MemoBorrowCalls

/-! Source-scoped runtime witnesses. Every normal callee retains its actual
parsed region-bearing local annotations, while the old exact-cost loan trace
is interpreted in the common retained-world call lifetime. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Regions

open LookupSource LookupSource.Heap LookupSource.Heap.Regions

def Valid (program : Program) (body : Function → MemoSource.Code) : Prop :=
  ∀ function, function ≠ .boxNew → ∃ decl ∈ program.definitions,
    decl.function = function ∧ decl.source.code = body function ∧ LookupSource.Heap.Borrow.codeRoutes decl.source.locals (body function) = true

def RunScoped (base : Memory) (program : Program) (body : Function → MemoSource.Code) : Nat → LookupSource.Heap.Frame.CallSafetyFor Function
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    if function = .boxNew then MemoSource.Heap.run body (fuel + 1) function cells memory = some (cell, after, cost)
    else ∃ decl ∈ program.definitions, decl.function = function ∧ ∃ inner,
      LookupSource.Heap.Borrow.Trace base (MemoSource.Heap.run body fuel) (RunScoped base program body fuel) decl.source.locals (Types.output function)
        (body function) memory (initialLocals cells) (.returned cell) after inner ∧
      EnvValue base memory (.body decl.bodyCount) (callLifetime base) decl.locals.types (initialLocals cells) ∧
      cost = (⟨1, entryEvents function⟩ : Cost).plus inner

theorem RunScoped.erases (base : Memory) (program : Program) (body : Function → MemoSource.Code) (fuel : Nat)
    {function : Function} {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunScoped base program body fuel function cells memory cell after cost) :
    MemoSource.Heap.run body fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    by_cases hf : function = .boxNew
    · simpa [RunScoped, hf] using h
    · simp only [RunScoped, hf, ite_false] at h
      obtain ⟨decl, _, _, inner, trace, _, rfl⟩ := h
      simp only [MemoSource.Heap.run, hf, ite_false, trace.erases, bind, Option.bind]

theorem run_scoped (base : Memory) (program : Program) (body : Function → MemoSource.Code)
    (hb : Valid program body) (fuel : Nat) :
    LookupSource.Heap.Borrow.CallsSafeWith Types.callOutput base (MemoSource.Heap.run body fuel) (RunScoped base program body fuel) := by
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
            exact ⟨LookupSource.Heap.Borrow.alloc_safe hvalue, Extends.append memory [_], by simpa [RunScoped] using hraw⟩
    · simp only [Types.callOutput, hf, ite_false] at ht
      split at ht
      next heq =>
        have heq := SourceTypes.sameList_eq heq
        subst types
        cases ht
        obtain ⟨decl, hd, hfn, hcode, hroutes⟩ := hb function hf
        have hdecl : decl.source.function = function := hfn
        have hprefix := decl.source.boundary
        have hconstraints := decl.source.constraints
        rw [hdecl] at hprefix hconstraints
        rw [hcode] at hconstraints
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
            obtain ⟨trace, hp, hex⟩ := LookupSource.Heap.Borrow.exec_safeWith ih (body function) hext
              (LookupSource.Heap.Borrow.initial_safe hargs hprefix) hconstraints hroutes hx
            refine ⟨hp, hex, ?_⟩
            simp only [RunScoped, hf, ite_false]
            exact ⟨decl, hd, hfn, inner, trace, LookupSource.Heap.Regions.trace_regional decl.locals trace, rfl⟩
      next => cases ht

theorem original_program_valid : ∃ program, read Input.Program.source = .ok program ∧ Valid program MemoSource.Program.body :=
  Certificate.original_program_routes

end SubtreeProofs.Rust.MemoSource.Regions
