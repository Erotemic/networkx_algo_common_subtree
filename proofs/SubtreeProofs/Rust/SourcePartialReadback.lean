module

public import SubtreeProofs.Rust.SourcePartialLocals

/-! Full-value place-read compatibility. The partial-local implementation
preserves the original source interpreter's reads on fully lifted states,
including shared/owned dereferences and variant-checked fields. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial

def projectValue (value : Value) : Projection → Option Value
  | .deref => match value with | .reference child | .boxed child => some child | _ => none
  | .field variant index => match value with
    | .node _ actual fields => if variant.all (· = actual) then fields[index]? else none
    | _ => none

def projectValues (value : Value) : List Projection → Option Value
  | [] => some value
  | first :: rest => do projectValues (← projectValue value first) rest

theorem projectValues_append (value : Value) (first last : List Projection) :
    projectValues value (first ++ last) = (do projectValues (← projectValues value first) last) := by
  induction first generalizing value with
  | nil => rfl
  | cons step rest ih =>
    simp only [List.cons_append, projectValues]
    cases hp : projectValue value step with
    | none => simp
    | some child => simpa only [bind, Option.bind] using ih child

theorem ofFields_getElem (fields : List Value) (index : Nat) :
    (ofFields fields)[index]? = fields[index]?.map Slot.ofValue := by
  induction index generalizing fields with
  | zero => cases fields <;> simp [ofFields]
  | succ index ih => cases fields <;> simp [ofFields, ih]

theorem Slot.get_ofValue (value : Value) (path : List Projection) :
    (Slot.ofValue value).get path = (projectValues value path).map Slot.ofValue := by
  induction path generalizing value with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | deref =>
      cases value with
      | boolean _ | number _ | node _ _ _ => simp [Slot.ofValue, Slot.get, projectValues, projectValue]
      | reference child | boxed child =>
        simpa only [Slot.ofValue, Slot.get, projectValues, projectValue, bind, Option.bind] using ih child
    | field variant index =>
      cases value with
      | boolean _ | number _ | reference _ | boxed _ => simp [Slot.ofValue, Slot.get, projectValues, projectValue]
      | node kind actual fields =>
        simp only [Slot.ofValue, Slot.get, projectValues, projectValue]
        by_cases hv : variant.all (· = actual) = true
        · simp only [hv, ite_true, ofFields_getElem]
          cases hf : fields[index]? with
          | none => simp
          | some child => simpa only [Option.map_some, bind, Option.bind] using ih child
        · simp [hv]

theorem Slot.read_ofValue (value : Value) (path : List Projection) :
    (Slot.ofValue value).read path = projectValues value path := by
  simp only [Slot.read, Slot.get_ofValue]
  cases hp : projectValues value path with
  | none => rfl
  | some child => simpa only [Option.map_some, bind, Option.bind] using Slot.materialize_ofValue child

theorem Slot.read_empty (path : List Projection) : Slot.empty.read path = none := by
  cases path with
  | nil => simp [Slot.read, Slot.get, Slot.materialize]
  | cons step rest => cases step <;> simp [Slot.read, Slot.get]

theorem readPlace_split (env : Env) (place : Place) :
    readPlace env place = (do projectValues (← env (splitPlace place).1) (splitPlace place).2) := by
  induction place with
  | «local» slot => simp [readPlace, splitPlace, projectValues]
  | deref parent ih =>
    rcases hp : splitPlace parent with ⟨slot, path⟩
    simp only [readPlace, ih, splitPlace, hp, projectValues_append]
    cases he : env slot with
    | none => rfl
    | some value =>
      simp only [bind, Option.bind]
      cases hr : projectValues value path with
      | none => rfl
      | some child => cases child <;> rfl
  | field parent variant index ih =>
    rcases hp : splitPlace parent with ⟨slot, path⟩
    simp only [readPlace, ih, splitPlace, hp, projectValues_append]
    cases he : env slot with
    | none => rfl
    | some value =>
      simp only [bind, Option.bind]
      cases hr : projectValues value path with
      | none => rfl
      | some child =>
        cases child <;> try rfl
        simp only [projectValues, projectValue]
        split <;> simp

theorem Locals.read_lift (env : Env) (place : Place) :
    (Locals.lift env).read place = readPlace env place := by
  rw [readPlace_split]
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [Locals.read, hp, Locals.lift]
  cases he : env slot with
  | none => simpa only [bind, Option.bind] using Slot.read_empty path
  | some value => simpa only [bind, Option.bind] using Slot.read_ofValue value path


theorem Locals.get_lift {env : Env} {place : Place} {value : Value}
    (hr : readPlace env place = some value) :
    ((Locals.lift env) (splitPlace place).1).get (splitPlace place).2 = some (Slot.ofValue value) := by
  rw [readPlace_split] at hr
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [hp] at hr ⊢
  cases he : env slot with
  | none => simp [he] at hr
  | some root =>
    simp only [he, bind, Option.bind] at hr
    simp only [Locals.lift, he, Slot.get_ofValue, hr, Option.map_some]

end SubtreeProofs.Rust.LookupSource.Partial
