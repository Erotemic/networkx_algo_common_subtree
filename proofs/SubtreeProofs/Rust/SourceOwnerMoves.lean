module

public import SubtreeProofs.Rust.SourceOwnerInventory

/-! Actual owned projections and finite activation owner conservation. A move
transfers the selected Box occurrences into its real returned cell, leaving
Box shells and siblings in the same stored root. Memory is unchanged. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

theorem locatePath_owned {memory : Memory} {cell moved : Cell} (pointer : Pointer) (path : List Projection)
    (h : ownedProjection memory cell path = some moved) :
    ∃ address, locatePath memory cell pointer path = some (moved, address) := by
  induction path generalizing cell pointer with
  | nil => cases h; exact ⟨pointer, rfl⟩
  | cons projection rest ih =>
    cases projection with
    | deref =>
      cases cell with
      | boolean _ | number _ | node _ _ _ | shared _ => cases h
      | owned address =>
        cases hr : memory[address]? with
        | none => simp [ownedProjection, hr] at h
        | some child =>
          obtain ⟨target, ht⟩ := ih ⟨address, []⟩ (by simpa only [ownedProjection, hr, Bind.bind, Option.bind] using h)
          exact ⟨target, by simpa only [locatePath, hr, Bind.bind, Option.bind] using ht⟩
    | field variant index =>
      cases cell with
      | boolean _ | number _ | shared _ | owned _ => cases h
      | node kind tag cells =>
        by_cases hv : variant.all (· = tag) = true
        · cases hr : cells[index]? with
          | none => simp [ownedProjection, hv, hr] at h
          | some child =>
            obtain ⟨target, ht⟩ := ih (pointer.field index)
              (by simpa only [ownedProjection, hv, ite_true, hr, Bind.bind, Option.bind] using h)
            exact ⟨target, by simpa only [locatePath, hv, ite_true, hr, Bind.bind, Option.bind] using ht⟩
        · simp [ownedProjection, hv] at h

namespace Storage

theorem locate_owned {world : World} {roots : Roots} {place : Place} {root moved : Cell}
    (hr : rawAt world roots (splitPlace place).1 = some root)
    (hp : ownedProjection world.memory root (splitPlace place).2 = some moved) :
    ∃ pointer, locate world roots place = some (moved, pointer) := by
  rcases hs : splitPlace place with ⟨slot, path⟩
  simp only [hs] at hr hp
  cases hb : roots slot with
  | none => simp [rawAt, hb] at hr
  | some binding =>
    have hc : world.memory[binding.address]? = some root := by simpa only [rawAt, hb, Bind.bind, Option.bind] using hr
    obtain ⟨pointer, ht⟩ := locatePath_owned ⟨binding.address, []⟩ path hp
    exact ⟨pointer, by simpa only [locate, hs, hb, hc, Bind.bind, Option.bind] using ht⟩

theorem Activation.move_owners {world : World} {active : Activation} (ha : active.Valid world)
    {place : Place} {value : Value} {after : Partial.Locals}
    (hm : active.state.move place = some (value, after)) :
    ∃ moved owners, (∃ pointer, locate world active.roots place = some (moved, pointer)) ∧
      Represents world.memory moved value ∧ Footprint world.memory moved owners ∧
      (active.owners world).Perm (owners ++ ({ active with state := after } : Activation).owners world) := by
  have hbound := Activation.move_root_lt ha hm
  obtain ⟨_, guards, hf⟩ := ha
  obtain ⟨root, moved, owners, remaining, hr, hp, hv, ho, he, hperm⟩ := hf.ownerState.move hm
  have hcollect := OwnerState.collect_partition (Addressed.ownerState world.memory (rawAt world active.roots) active.state)
    (List.range active.count) (List.nodup_range) (splitPlace place).1 (List.mem_range.mpr hbound) owners remaining hperm
  have canonical := he.ownerState
  refine ⟨moved, owners, locate_owned hr hp, hv, ho, ?_⟩
  simpa only [Activation.owners, canonical] using hcollect

end Storage

end SubtreeProofs.Rust.LookupSource.Partial.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem copyCell_owners {memory : Memory} {cell copied : Cell} (h : copyCell cell = some copied) : Footprint memory copied [] := by
  cases cell with
  | boolean b | shared b => cases h; constructor
  | number n =>
    simp only [copyCell] at h
    split at h
    next => cases h; exact .number n
    next => cases h
  | node _ _ _ | owned _ => cases h

theorem operand_owners {world : World} {active : Activation} (ha : active.Valid world)
    {guarded : List Nat} {op : Operand} {packet : ValueCell} {after : State}
    (h : operand world active.roots guarded active.state op = some (packet, after)) :
    ∃ owners, Footprint world.memory packet.1 owners ∧
      (active.owners world).Perm (owners ++ ({ active with state := after } : Activation).owners world) := by
  cases op with
  | move place =>
    obtain ⟨pointer, hm, hl, _⟩ := operand_move_iff.mp h
    obtain ⟨moved, owners, ⟨address, ht⟩, _, ho, hp⟩ := Activation.move_owners ha hm
    have he := Option.some.inj (hl.symm.trans ht)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨owners, ho, hp⟩
  | copy place =>
    cases hr : read world active.roots active.state place with
    | none => simp [operand, hr] at h
    | some pair =>
      rcases pair with ⟨⟨cell, value⟩, pointer⟩
      cases hc : copyCell cell with
      | none => simp [operand, hr, hc] at h
      | some copied =>
        simp only [operand, hr, hc, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], copyCell_owners hc, by simp⟩
  | boolean b =>
    cases h
    exact ⟨[], .boolean b, by simp⟩
  | number n =>
    simp only [operand] at h
    split at h
    next => cases h; exact ⟨[], .number n, by simp⟩
    next => cases h

end SubtreeProofs.Rust.SourceEval.Addressed
