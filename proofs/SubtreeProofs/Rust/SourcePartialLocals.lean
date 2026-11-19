module

public import SubtreeProofs.Rust.SourcePartialMoves

/-! Local partial moves and whole-local conditional destruction. These
primitives support the evaluator's observed normal drop places. Logical drop
work counts retained structure and Boxes; source glue/heap adequacy is separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial

def splitPlace : Place → Nat × List Projection
  | .local slot => (slot, [])
  | .deref parent => let (slot, path) := splitPlace parent; (slot, path ++ [.deref])
  | .field parent variant index => let (slot, path) := splitPlace parent; (slot, path ++ [.field variant index])

abbrev Locals := Nat → Slot

def Locals.set (env : Locals) (slot : Nat) (part : Slot) : Locals :=
  fun index => if index = slot then part else env index

def Locals.lift (env : Env) : Locals := fun slot =>
  match env slot with | none => .empty | some value => Slot.ofValue value

theorem Locals.lift_materialize (env : Env) (slot : Nat) : ((Locals.lift env) slot).materialize = env slot := by
  cases h : env slot with
  | none => simp only [lift, h, Slot.materialize]
  | some value => simpa only [lift, h] using Slot.materialize_ofValue value

def Locals.read (env : Locals) (place : Place) : Option Value :=
  let (slot, path) := splitPlace place
  (env slot).read path

def Locals.move (env : Locals) (place : Place) : Option (Value × Locals) := do
  let (slot, path) := splitPlace place
  let (value, remaining) ← (env slot).take path
  some (value, env.set slot remaining)

def Locals.drop (env : Locals) (slot : Nat) : Locals × DropWork :=
  (env.set slot .empty, (env slot).dropWork)

theorem Locals.move_spec {env after : Locals} {place : Place} {value : Value}
    (ht : env.move place = some (value, after)) :
    env.read place = some value ∧
      ∃ remaining, after = env.set (splitPlace place).1 remaining ∧
        remaining.get (splitPlace place).2 = some .empty ∧
        (env (splitPlace place).1).dropWork = (Slot.ofValue value).dropWork.plus remaining.dropWork := by
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [move, hp] at ht
  cases hm : (env slot).take path with
  | none => simp [hm] at ht
  | some pair =>
    rcases pair with ⟨result, remaining⟩
    simp only [hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨by simpa only [read, hp] using (env slot).take_read path hm,
      remaining, rfl, (env slot).take_hole path hm, (env slot).take_work path hm⟩

theorem Locals.move_other {env after : Locals} {place : Place} {value : Value}
    (ht : env.move place = some (value, after)) (slot : Nat) (hne : slot ≠ (splitPlace place).1) :
    after slot = env slot := by
  obtain ⟨_, remaining, rfl, _, _⟩ := move_spec ht
  simp only [set, hne, ite_false]

theorem Locals.drop_spec (env : Locals) (slot : Nat) :
    (env.drop slot).1 slot = .empty ∧ (env.drop slot).2 = (env slot).dropWork ∧
      ∀ other, other ≠ slot → (env.drop slot).1 other = env other := by
  exact ⟨by simp [drop, set], rfl, fun other h => by simp [drop, set, h]⟩

theorem Locals.drop_twice (env : Locals) (slot : Nat) :
    ((env.drop slot).1.drop slot).2 = {} := by
  simp only [drop, set, ite_true, Slot.dropWork]

theorem Locals.move_local_lift (env : Env) (slot : Nat) :
    (Locals.lift env).move (.local slot) =
      (evalOperand env (.move slot)).map (fun (value, after) => (value, Locals.lift after)) := by
  cases hs : env slot with
  | none => simp [move, splitPlace, lift, Slot.take, Slot.materialize, evalOperand, hs]
  | some value =>
    simp only [move, splitPlace, lift, hs, Slot.take, Slot.materialize_ofValue, evalOperand,
      bind, Option.bind, Option.map_some]
    congr 1
    congr 1
    funext index
    by_cases hi : index = slot
    · simp only [set, lift, hi, ite_true, Env.set]
    · simp only [set, lift, hi, ite_false, Env.set]

end SubtreeProofs.Rust.LookupSource.Partial
