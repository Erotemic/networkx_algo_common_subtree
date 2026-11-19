module

public import SubtreeProofs.Rust.LookupSpatialExecution
public import SubtreeProofs.Rust.MemoFrameCalls
public import SubtreeProofs.Rust.MemoTypeCalls

/-! Intermediate separation for actual memo helper calls, including the owned
input table and all suspended caller owners. Initial locals retain the exact
argument occurrence list instead of dropping it through an all-plain shortcut. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

theorem values_none (count : Nat) : values count (fun _ => none) = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change values count (tail (fun _ => none)) = []
    exact ih

theorem values_list (cells : List Cell) (count : Nat) (hc : cells.length ≤ count) :
    values count (fun index => cells[index]?) = cells := by
  induction cells generalizing count with
  | nil => simpa using values_none count
  | cons cell cells ih => cases count with
    | zero => simp at hc
    | succ count =>
      have ht : tail (fun index => (cell :: cells)[index]?) = (fun index => cells[index]?) := rfl
      simp only [values, List.getElem?_cons_zero, Option.toList_some, List.singleton_append, ht]
      exact congrArg (cell :: ·) (ih count (by simp only [List.length_cons] at hc; omega))

theorem values_initial (cells : List Cell) (count : Nat) (hc : cells.length + 1 ≤ count) :
    values count (initialLocals cells) = cells := by
  cases count with
  | zero => omega
  | succ count =>
    have ht : tail (initialLocals cells) = (fun index => cells[index]?) := by
      funext index
      simp [tail, initialLocals]
    simp only [values, initialLocals, ite_true, Option.toList_none, List.nil_append]
    change values count (tail (initialLocals cells)) = cells
    rw [ht]
    exact values_list cells count (by omega)

end SubtreeProofs.Rust.LookupSource.Heap.Spatial

namespace SubtreeProofs.Rust.MemoSource.Spatial

open LookupSource LookupSource.Heap LookupSource.Heap.Spatial

abbrev CallsSpatial (call : CallsFor Function) (good : LookupSource.Heap.Frame.CallSafetyFor Function) :=
  CallsSpatialWith Frame.ArgsMatch call good

def RunSpatial (body : Function → Code) : Nat → LookupSource.Heap.Frame.CallSafetyFor Function
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    MemoSource.Heap.run body (fuel + 1) function cells memory = some (cell, after, cost) ∧
    if function = .boxNew then True else
      ∃ count inner, cost = (⟨1, entryEvents function⟩ : Cost).plus inner ∧
        ∀ frame, Separated memory (cells ++ frame) →
          Trace (MemoSource.Heap.run body fuel) (RunSpatial body fuel) count frame (body function)
            memory (initialLocals cells) (.returned cell) after inner

theorem RunSpatial.erases (body : Function → Code) (fuel : Nat) {function : Function}
    {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunSpatial body fuel function cells memory cell after cost) :
    MemoSource.Heap.run body fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel => exact h.1

theorem initial_bounded {cells : List Cell} {count : Nat} (h : cells.length + 1 ≤ count) :
    Bounded count (initialLocals cells) := by
  intro index hi
  have hn : index ≠ 0 := by omega
  simp only [initialLocals, hn, ite_false]
  apply List.getElem?_eq_none_iff.mpr
  omega

theorem boundary_bound {function : Function} (hf : function ≠ .boxNew) {locals : List Ty} {cells : List Cell}
    (hargs : Frame.ArgsMatch function cells)
    (hb : locals.take ((Types.inputs function).length + 1) = Types.output function :: Types.inputs function) :
    cells.length + 1 ≤ locals.length := by
  have hlen := congrArg List.length hb
  have hle := List.length_take_le' ((Types.inputs function).length + 1) locals
  have ha := hargs.1
  have hi : (Types.inputs function).length = arity function := by
    cases function <;> simp_all [Types.inputs, arity]
  simp only [List.length_cons] at hlen
  omega

theorem run_spatial (body : Function → Code) (padding : Nat)
    (hframe : Frame.BodyChecked body padding) (htypes : Types.BodiesTyped body) (fuel : Nat) :
    CallsSpatial (MemoSource.Heap.run body fuel) (RunSpatial body fuel) := by
  induction fuel with
  | zero => intro function cells memory cell after cost _ hr; cases hr
  | succ fuel ih =>
    intro function cells memory cell after cost hargs hr
    by_cases hf : function = .boxNew
    · subst function
      have hraw := hr
      simp only [MemoSource.Heap.run, ite_true] at hr
      cases cells with
      | nil => cases hr
      | cons value rest => cases rest with
        | cons _ _ => cases hr
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          refine ⟨⟨hraw, by trivial⟩, ?_⟩
          intro frame hs
          exact ⟨hs.alloc, Extends.append memory [_]⟩
    · obtain ⟨locals, hprefix, hcode⟩ := htypes function hf
      have hbound := boundary_bound hf hargs hprefix
      have hb := initial_bounded hbound
      have hfields : LookupSource.Heap.Frame.FieldsMatch (Frame.inputFlags function) cells := by
        rcases hargs.2 with hbox | hm
        · exact False.elim (hf hbox)
        · exact hm
      have hc : LookupSource.Heap.Frame.CallSoundWith Frame.ArgsMatch Frame.outputFlag
          (MemoSource.Heap.run body fuel) (RunSpatial body fuel) := by
        intro fn args mem value final charge ha hh
        exact ⟨(Frame.run_sound body padding hframe fuel fn args mem value final charge ha hh).1,
          (ih fn args mem value final charge ha hh).1⟩
      have hraw := hr
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
          have hg := (LookupSource.Heap.Frame.verify_soundWith
            (profile := Frame.callProfile) (resultFlag := Frame.outputFlag) (argsMatch := Frame.ArgsMatch)
            (fun fn _ _ hm hp => Frame.profile_sound (function := fn) hm hp) hc
            (body function) (fun _ => false) (Frame.outputFlag function) (hframe function hf)
            (LookupSource.Heap.Frame.initial_rep padding hfields) hx).1
          have hw (frame : List Cell) (hs : Separated memory (cells ++ frame)) :
              Trace (MemoSource.Heap.run body fuel) (RunSpatial body fuel) locals.length frame (body function)
                  memory (initialLocals cells) (.returned value) mem inner ∧
                Separated mem (value :: frame) ∧ Extends memory mem := by
            apply exec_spatialWith (calleeOutput := Types.callOutput) ih hg hcode hb
            simpa only [values_initial cells locals.length hbound] using hs
          refine ⟨⟨hraw, ?_⟩, fun frame hs => (hw frame hs).2⟩
          simp only [hf, ite_false]
          exact ⟨locals.length, inner, rfl, fun frame hs => (hw frame hs).1⟩

theorem original_spatial (fuel : Nat) : CallsSpatial (MemoSource.Heap.run Program.body fuel) (RunSpatial Program.body fuel) :=
  run_spatial Program.body 15 Frame.original_checked Types.original_bodies_typed fuel

end SubtreeProofs.Rust.MemoSource.Spatial
