module

public import SubtreeProofs.Rust.LookupSpatialExecution
public import SubtreeProofs.Rust.LookupTypeCalls
public import SubtreeProofs.Rust.LookupFrameCalls

/-! Spatial traces through every actual recursive call. The arbitrary frame
includes suspended caller locals, so nested allocations remain separated from
all active callers. Shared input aliases are allowed. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

theorem plainFields_get {cells : List Cell} (h : Frame.PlainFields cells) (index : Nat) {cell : Cell}
    (hc : cells[index]? = some cell) : Frame.Plain cell := by
  induction index generalizing cells with
  | zero => cases h with
    | nil => cases hc
    | cons first rest => cases hc; exact first
  | succ index ih => cases h with
    | nil => cases hc
    | cons first rest => exact ih rest hc

theorem initial_plain {cells : List Cell} (h : Frame.PlainFields cells) (index : Nat) :
    Frame.Disposable (initialLocals cells index) := by
  by_cases hi : index = 0
  · simp [initialLocals, hi, Frame.Disposable]
  · simp only [initialLocals, hi, ite_false]
    cases hc : cells[index - 1]? with
    | none => trivial
    | some cell => exact plainFields_get h _ hc

theorem initial_bounded {cells : List Cell} {count : Nat} (h : cells.length + 1 ≤ count) :
    Bounded count (initialLocals cells) := by
  intro index hi
  have hn : index ≠ 0 := by omega
  simp only [initialLocals, hn, ite_false]
  apply List.getElem?_eq_none_iff.mpr
  omega

theorem boundary_bound {function : Function} (hf : function ≠ .boxNew) {locals : List Ty} {cells : List Cell}
    (hargs : Frame.ArgsMatch function cells)
    (hb : locals.take ((SourceTypes.inputs function).length + 1) =
      SourceTypes.output function :: SourceTypes.inputs function) : cells.length + 1 ≤ locals.length := by
  have hlen := congrArg List.length hb
  have hle := List.length_take_le' ((SourceTypes.inputs function).length + 1) locals
  have harity : (SourceTypes.inputs function).length = Frame.arity function := by
    cases function <;> simp_all [SourceTypes.inputs, Frame.arity]
  have ha := hargs.1
  simp only [List.length_cons] at hlen
  omega

def RunSpatial (body : Function → Code) : Nat → Frame.CallSafety
  | 0, _, _, _, _, _, _ => False
  | fuel + 1, function, cells, memory, cell, after, cost =>
    Heap.run body (fuel + 1) function cells memory = some (cell, after, cost) ∧
    if function = .boxNew then True else
      ∃ count inner, cost = (⟨1, entryEvents function⟩ : Cost).plus inner ∧
        ∀ frame, Separated memory (cells ++ frame) →
          Trace (Heap.run body fuel) (RunSpatial body fuel) count frame (body function)
            memory (initialLocals cells) (.returned cell) after inner

theorem RunSpatial.erases (body : Function → Code) (fuel : Nat) {function : Function}
    {cells : List Cell} {memory after : Memory} {cell : Cell} {cost : Cost}
    (h : RunSpatial body fuel function cells memory cell after cost) :
    Heap.run body fuel function cells memory = some (cell, after, cost) := by
  cases fuel with
  | zero => cases h
  | succ fuel => exact h.1

theorem run_spatial (body : Function → Code) (padding : Nat)
    (hframe : Frame.BodyChecked body padding) (htypes : SourceTypes.BodiesTyped body) (fuel : Nat) :
    CallsSpatial (Heap.run body fuel) (RunSpatial body fuel) := by
  induction fuel with
  | zero => intro function cells memory cell after cost _ hr; cases hr
  | succ fuel ih =>
    intro function cells memory cell after cost hargs hr
    by_cases hf : function = .boxNew
    · subst function
      have hrun := hr
      simp only [Heap.run, ite_true] at hr
      cases cells with
      | nil => cases hr
      | cons value rest => cases rest with
        | cons _ _ => cases hr
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          refine ⟨⟨hrun, by trivial⟩, ?_⟩
          intro frame hs
          exact ⟨hs.alloc, Extends.append memory [_]⟩
    · have hp : Frame.PlainFields cells := by
        have hm : Frame.FieldsMatch (Frame.inputFlags function) cells := by
          rcases hargs.2 with hbox | hm
          · exact False.elim (hf hbox)
          · exact hm
        have hflags : (Frame.inputFlags function).any id = false := by simp [Frame.inputFlags]
        exact hm.plain hflags
      obtain ⟨locals, hprefix, hcode⟩ := htypes function hf
      have hb : Bounded locals.length (initialLocals cells) := initial_bounded (boundary_bound hf hargs hprefix)
      have hraw := hr
      have hg := (Frame.run_sound body padding hframe (fuel + 1) _ _ _ _ _ _ hargs hr).2
      simp only [Frame.RunSafe, hf, ite_false] at hg
      obtain ⟨inner, hguard, hcost⟩ := hg
      have hguard' : Frame.Guarded (Heap.run body fuel) (RunSpatial body fuel) (body function)
          memory (initialLocals cells) (.returned cell) after inner := by
        have hc : Frame.CallSound (Heap.run body fuel) (RunSpatial body fuel) := by
          intro fn args mem value final charge ha hh
          exact ⟨(Frame.run_sound body padding hframe fuel fn args mem value final charge ha hh).1,
            (ih fn args mem value final charge ha hh).1⟩
        exact (Frame.verify_sound hc (body function) (fun _ => false) (Frame.outputFlag function)
          (hframe function hf) (Frame.initial_rep padding (by
            rcases hargs.2 with hbox | hm
            · exact False.elim (hf hbox)
            · exact hm)) hguard.erases).1
      have hw (frame : List Cell) (hs : Separated memory (cells ++ frame)) :
          Trace (Heap.run body fuel) (RunSpatial body fuel) locals.length frame (body function)
              memory (initialLocals cells) (.returned cell) after inner ∧
            Separated after (cell :: frame) ∧ Extends memory after := by
        have hframe' : Separated memory frame := (Separated.plain_fields hp).mp hs
        have hs' : Separated memory (values locals.length (initialLocals cells) ++ frame) :=
          (Separated.plain_fields (plain_values (fun index => initial_plain hp index))).mpr hframe'
        exact exec_spatial ih hguard' hcode hb hs'
      refine ⟨⟨hraw, ?_⟩, fun frame hs => (hw frame hs).2⟩
      simp only [hf, ite_false]
      exact ⟨locals.length, inner, hcost, fun frame hs => (hw frame hs).1⟩

theorem original_spatial (fuel : Nat) : CallsSpatial (Heap.run Program.body fuel) (RunSpatial Program.body fuel) :=
  run_spatial Program.body 20 Frame.original_checked SourceTypes.original_bodies_typed fuel

theorem mutant_spatial (fuel : Nat) : CallsSpatial (Heap.run ExtraCompare.body fuel) (RunSpatial ExtraCompare.body fuel) :=
  run_spatial ExtraCompare.body 20 Frame.mutant_checked SourceTypes.mutant_bodies_typed fuel

end SubtreeProofs.Rust.LookupSource.Heap.Spatial
