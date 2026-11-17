module

public import SubtreeProofs.Rust.SourceEvalAddressedExpressions
public import SubtreeProofs.Rust.SourceHeapGraphTrace
public import SubtreeProofs.Rust.SourceEvalFrameActions

/-! One-pass addressed RHS evaluation and destination initialization. Move
protection and retained store contexts are distinct resources. The RHS graph is
traced from concrete cells/metadata before a guarded write; source action and
frame correspondence follow independently from execution. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def emptySlot : Slot → Bool
  | .empty => true
  | _ => false

theorem emptySlot_iff (part : Slot) : emptySlot part = true ↔ part = .empty := by
  cases part <;> simp [emptySlot]

def assign (world : World) (roots : Roots) (frame : Nat) (blocked retained : List Nat)
    (state : State) (slot : Nat) (rhs : Expr) : Option (World × State) := do
  let ((cell, value), middle) ← expression world roots blocked state rhs
  if emptySlot (middle slot) then
    let binding ← roots slot
    let used ← traceGraph world.memory cell value
    let after ← world.writeStack frame slot binding (retained ++ used) cell
    some (after, middle.set slot (Slot.ofValue value))
  else none

theorem assign_run {world : World} {roots : Roots} {frame slot : Nat} {blocked retained used : List Nat}
    {state middle : State} {rhs : Expr} {cell : Heap.Cell} {value : Value} {binding : Binding} {after : World}
    (hr : expression world roots blocked state rhs = some ((cell, value), middle)) (he : middle slot = .empty)
    (hb : roots slot = some binding) (ht : traceGraph world.memory cell value = some used)
    (hw : world.writeStack frame slot binding (retained ++ used) cell = some after) :
    assign world roots frame blocked retained state slot rhs = some (after, middle.set slot (Slot.ofValue value)) := by
  simp only [assign, hr, he, emptySlot, hb, ht, hw, Bind.bind, Option.bind, ↓reduceIte]

theorem assign_spec {world final : World} {frame slot : Nat} {roots : Roots} {state after : State}
    {guards blocked retained : List Nat} (hf : Frame world frame roots state guards) (hw : world.WellFormed)
    (call : Calls) (rhs : Expr)
    (context : ∀ cell value middle, expression world roots blocked state rhs = some ((cell, value), middle) →
      Frame world frame (roots.set slot none) (middle.set slot .empty) retained)
    (h : assign world roots frame blocked retained state slot rhs = some (final, after)) :
    ∃ (cell : Heap.Cell) (value : Value) (middle : State) (used : List Nat) (binding : Binding),
      expression world roots blocked state rhs = some ((cell, value), middle) ∧ roots slot = some binding ∧
      SourceEval.action call state (.assign slot rhs) = some (after, Cost.local (Action.assign slot rhs).weight) ∧
      final = world.write binding.address cell ∧ after = middle.set slot (Slot.ofValue value) ∧
      Frame final frame roots after (retained ++ used ++ [binding.address]) ∧
      Graph final.memory cell value used ∧ Preserves world final retained ∧ final.WellFormed := by
  unfold assign at h
  cases hr : expression world roots blocked state rhs with
  | none => simp [hr] at h
  | some result =>
    rcases result with ⟨⟨cell, value⟩, middle⟩
    by_cases he : emptySlot (middle slot) = true
    · cases hb : roots slot with
      | none => simp [hr, hb] at h
      | some binding =>
        cases ht : traceGraph world.memory cell value with
        | none => simp [hr, he, hb, ht] at h
        | some used =>
          cases hwrite : world.writeStack frame slot binding (retained ++ used) cell with
          | none => simp [hr, he, hb, ht, hwrite] at h
          | some next =>
            simp only [hr, he, hb, ht, hwrite, Bind.bind, Option.bind, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨actual, hs, hg, hu, hm⟩ := expression_spec hf hr
            have hused : actual = used := Option.some.inj (hg.trace.symm.trans ht)
            subst used
            obtain ⟨hc, hl, _, hsep, rfl⟩ := World.writeStack_iff.mp hwrite
            have hstate := emptySlot_iff _ |>.mp he
            have hframe := Frame.store hw hb hstate (context cell value middle hr) hc hl hg.partial
              (fun a ha => hf.alive a (hu ha)) hsep
            have hleft : binding.address ∉ retained := fun ha => hsep (List.mem_append_left _ ha)
            have hright : binding.address ∉ actual := fun ha => hsep (List.mem_append_right _ ha)
            refine ⟨cell, value, middle, actual, binding, rfl, rfl, ?_, rfl, rfl, hframe.2.2,
              hg.transport (world.write_preserves hright cell).reads, world.write_preserves hleft cell, hw.write _ _⟩
            simp only [SourceEval.action, hs, Bind.bind, Option.bind]
    · simp only [hr, he, Bind.bind, Option.bind, ↓reduceIte, reduceCtorEq] at h

theorem assign_complete {world : World} {frame slot : Nat} {roots : Roots} {state middle : State}
    {guards blocked retained used : List Nat} (hf : Frame world frame roots state guards) (hw : world.WellFormed)
    {rhs : Expr} {cell : Heap.Cell} {value : Value} {binding : Binding}
    (hr : expression world roots blocked state rhs = some ((cell, value), middle)) (he : middle slot = .empty)
    (hb : roots slot = some binding) (ht : traceGraph world.memory cell value = some used)
    (hsep : binding.address ∉ retained ++ used) :
    assign world roots frame blocked retained state slot rhs =
      some (world.write binding.address cell, middle.set slot (Slot.ofValue value)) := by
  obtain ⟨_, _, _, _, hm⟩ := expression_spec hf hr
  obtain ⟨_, _, _, hc, _, hu⟩ := hm.get hb
  have hl := hm.alive binding.address (hu (List.mem_append_right _ (by simp)))
  exact assign_run hr he hb ht (world.writeStack_success hw hc hl hsep cell)

end SubtreeProofs.Rust.SourceEval.Addressed
