module

public import SubtreeProofs.Rust.LookupBorrowLoans

/-! Address-origin preservation for source places. Crossing a shared reference
restores a view in the retained caller heap; subsequent owned dereferences and
field projections remain in that view. Fresh owned roots do not gain a loan. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

theorem fieldsSafe_get {base current : Memory} {cells : List Cell} {types : List Ty}
    (h : FieldsSafe base current cells types) (index : Nat) {cell : Cell} {ty : Ty}
    (hc : cells[index]? = some cell) (ht : types[index]? = some ty) : Safe base current cell ty := by
  induction index generalizing cells types with
  | zero => cases h with
    | nil => cases hc
    | cons first rest => cases hc; cases ht; exact first
  | succ index ih => cases h with
    | nil => cases hc
    | cons first rest => exact ih rest hc ht

theorem fromShared_heapBorrow {locals : List Ty} (place : Place) (h : fromShared locals place = true) :
    heapBorrow place = true := by
  induction place with
  | «local» slot => cases h
  | deref parent ih => rfl
  | field parent variant index ih => exact ih h

theorem locate_safe {base current : Memory} (hext : Extends base current) {locals : List Ty} {env : Locals}
    (he : EnvSafe base current locals env) (place : Place) {ty : Ty} {cell : Cell} {address : Option Pointer}
    (ht : SourceTypes.inferPlace locals place = some ty)
    (hr : locate current env place = some (cell, address)) :
    Safe base current cell ty ∧ (fromShared locals place = true → Typed base cell ty ∧
      ∀ pointer, address = some pointer → read base pointer = some cell) := by
  induction place generalizing ty cell address with
  | «local» slot =>
    simp only [locate] at hr
    cases hc : env slot with
    | none => simp [hc] at hr
    | some value =>
      simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨he.get hc ht, by intro h; cases h⟩
  | deref parent ih =>
    simp only [SourceTypes.inferPlace] at ht
    cases hs : SourceTypes.inferPlace locals parent with
    | none => simp [hs] at ht
    | some parentTy =>
      simp only [hs, bind, Option.bind] at ht
      simp only [locate] at hr
      cases hp : locate current env parent with
      | none => simp [hp] at hr
      | some pair =>
        rcases pair with ⟨value, loc⟩
        obtain ⟨hv, hold⟩ := ih hs hp
        cases hv with
        | boolean _ => cases ht
        | number _ => cases ht
        | node shape fields => cases shape <;> cases ht
        | @shared pointer inner loan =>
          simp only [SourceTypes.deref, Option.some.injEq] at ht
          subst ty
          obtain ⟨child, hread, htyped⟩ := loan.valid
          have hcurrent := read_extends hext hread
          simp only [hp, bind, Option.bind, hcurrent, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨from_base hext htyped, fun _ => ⟨htyped, by intro p h; cases h; exact hread⟩⟩
        | @owned pointer child inner hread hchild =>
          simp only [SourceTypes.deref, Option.some.injEq] at ht
          subst ty
          simp only [hp, bind, Option.bind, hread, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨hchild, ?_⟩
          intro hfrom
          have hpast : fromShared locals parent = true := by simpa only [fromShared, hs] using hfrom
          obtain ⟨htyped, _⟩ := hold hpast
          cases htyped with
          | owned hpast htyped =>
            have he : _ = child := Option.some.inj ((hext _ _ hpast).symm.trans hread)
            subst child
            exact ⟨htyped, by intro p h; cases h; simpa [read, fields] using hpast⟩
  | field parent variant index ih =>
    simp only [SourceTypes.inferPlace] at ht
    cases hs : SourceTypes.inferPlace locals parent with
    | none => simp [hs] at ht
    | some parentTy =>
      simp only [hs, bind, Option.bind] at ht
      simp only [locate] at hr
      cases hp : locate current env parent with
      | none => simp [hp] at hr
      | some pair =>
        rcases pair with ⟨value, loc⟩
        obtain ⟨hv, hold⟩ := ih hs hp
        simp only [hp, bind, Option.bind] at hr
        cases hv <;> simp only at hr <;> try contradiction
        rename_i kind actual cells types fields shape
        split at hr
        next hg =>
          cases hc : cells[index]? with
          | none => simp [hc] at hr
          | some value =>
            simp only [hc, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            refine ⟨fieldsSafe_get fields index hc (SourceTypes.projection_fields shape hg ht), ?_⟩
            intro hfrom
            obtain ⟨hpast, haddr⟩ := hold hfrom
            cases hpast with
            | node shape fields =>
              refine ⟨SourceTypes.fieldsTyped_get fields index hc (SourceTypes.projection_fields shape hg ht), ?_⟩
              intro pointer ha
              cases loc with
              | none => simp at ha
              | some address =>
                simp only [Option.map_some, Option.some.injEq] at ha
                subst pointer
                rw [read_field (haddr address rfl)]
                exact hc
        next => contradiction

theorem borrow_safe {base current : Memory} (hext : Extends base current) {locals : List Ty} {env : Locals}
    (he : EnvSafe base current locals env) (place : Place) {ty : Ty} {cell : Cell}
    (ht : SourceTypes.inferPlace locals place = some ty) (hfrom : fromShared locals place = true)
    (hr : borrow current env place = some cell) :
    Safe base current cell (.shared ty) := by
  unfold borrow at hr
  cases hl : locate current env place with
  | none => simp [hl] at hr
  | some pair =>
    rcases pair with ⟨value, address⟩
    obtain ⟨htyped, haddr⟩ := (locate_safe hext he place ht hl).2 hfrom
    obtain ⟨pointer, rfl⟩ := locate_has_address place (fromShared_heapBorrow place hfrom) hl
    simp only [hl, bind, Option.bind] at hr
    cases hr
    exact .shared ⟨⟨value, haddr pointer rfl, htyped⟩⟩

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
