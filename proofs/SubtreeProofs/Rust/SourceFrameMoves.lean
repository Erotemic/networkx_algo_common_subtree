module

public import SubtreeProofs.Rust.SourceHeapGraphMoves
public import SubtreeProofs.Rust.SourceFrameUpdates

/-! Initialized concrete place reads and remaining source frames after moves.
Frames retain conservative read resources; the executable move policy separately
checks conflicts with protected reference roots. Ownership separation and actual
coverage of those protected roots remain trace invariants. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open LookupSource.Heap

theorem Frame.locate {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (place : Place) {value : Value} (hr : state.read place = some value) :
    ∃ cell pointer used, Storage.locate world roots place = some (cell, pointer) ∧
      Graph world.memory cell value used ∧ used ++ [pointer.root] ⊆ guards := by
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [Partial.Locals.read, hp] at hr
  cases hb : roots slot with
  | none =>
    have he : state slot = .empty := by simpa only [hb] using h.slots slot
    rw [he, Slot.read_empty] at hr
    cases hr
  | some binding =>
    obtain ⟨cell, used, hc, _, hg, hs⟩ := h.get hb
    have hread : read world.memory ⟨binding.address, []⟩ = some cell := by
      simp only [Heap.read, hc, Bind.bind, Option.bind, Heap.fields]
    obtain ⟨found, pointer, selected, hl, _, hg', hsub⟩ := hg.read ⟨binding.address, []⟩ hread path hr
    exact ⟨found, pointer, selected, by simp only [Storage.locate, hp, hb, hc, hl, Bind.bind, Option.bind], hg',
      fun _ ha => hs (hsub ha)⟩

theorem Frame.move {world : World} {frame : Nat} {roots : Roots} {state after : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) {place : Place} {value : Value}
    (ht : state.move place = some (value, after)) : Frame world frame roots after guards := by
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [Partial.Locals.move, hp] at ht
  cases hs : (state slot).take path with
  | none => simp [hs] at ht
  | some pair =>
    rcases pair with ⟨result, remaining⟩
    simp only [hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    cases hb : roots slot with
    | none =>
      have he : state slot = .empty := by simpa only [hb] using h.slots slot
      rw [he, take_empty] at hs
      cases hs
    | some binding =>
      obtain ⟨cell, all, hc, ht, hg, hu⟩ := h.get hb
      obtain ⟨_, first, rest, _, _, hr, hperm⟩ := hg.take path hs
      refine ⟨h.alive, ?_⟩
      intro index
      by_cases hi : index = slot
      · subst index
        simp only [hb, Partial.Locals.set, ite_true]
        refine ⟨cell, rest, hc, ht, hr, ?_⟩
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hu (List.mem_append_left _ (hperm.symm.subset (List.mem_append_right _ ha)))
        · exact hu (List.mem_append_right _ ha)
      · simpa only [Partial.Locals.set, hi, ite_false] using h.slots index

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
