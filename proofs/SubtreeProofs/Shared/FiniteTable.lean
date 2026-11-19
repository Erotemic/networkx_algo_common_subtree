module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Materialized finite tables for dependency-ordered recurrence evaluation

Each round maps an explicit complete key list and reads only the preceding
association table. The proof is independent of any tree or scoring model.
-/

@[expose] public section

namespace SubtreeProofs.FiniteTable

variable {A B : Type*} [DecidableEq A]

abbrev Table (A B : Type*) := List (A × B)

def read (fallback : B) (table : Table A B) (key : A) : B :=
  (table.lookup key).getD fallback

def rounds (keys : List A) (fallback : B) (update : (A → B) → A → B) : Nat → Table A B
  | 0 => []
  | fuel + 1 =>
    let previous := rounds keys fallback update fuel
    keys.map (fun key => (key, update (read fallback previous) key))

theorem read_map (fallback : B) (keys : List A) (f : A → B) {key : A} (h : key ∈ keys) :
    read fallback (keys.map (fun a => (a,f a))) key = f key := by
  simp [read, List.lookup_graph f h]

theorem rounds_length (keys : List A) (fallback : B) (update : (A → B) → A → B) (fuel : Nat) :
    (rounds keys fallback update fuel).length = if fuel = 0 then 0 else keys.length := by
  cases fuel <;> simp [rounds]

/-- The given rank need only decrease on genuine dependencies. Updates may
read additional entries if their result is independent of those entries. -/
theorem rounds_correct (keys : List A) (fallback : B) (update : (A → B) → A → B)
    (complete : ∀ key, key ∈ keys) (depends : A → A → Prop) (rank : A → Nat)
    (decreases : ∀ child parent, depends child parent → rank child < rank parent)
    (target : A → B)
    (hupdate : ∀ previous key, (∀ child, depends child key → previous child = target child) →
      update previous key = target key)
    (fuel : Nat) (key : A) (hrank : rank key < fuel) :
    read fallback (rounds keys fallback update fuel) key = target key := by
  induction fuel generalizing key with
  | zero => omega
  | succ fuel ih =>
    rw [rounds, read_map fallback keys _ (complete key)]
    apply hupdate
    intro child hc
    apply ih
    have hd := decreases child key hc
    omega

variable [LinearOrder B] [OrderBot B]

def maximum (keys : List A) (value : A → B) : B := (keys.map value).foldr max ⊥

theorem maximum_eq_sup (keys : List A) (value : A → B) :
    maximum keys value = keys.toFinset.sup value := by
  induction keys with
  | nil => simp [maximum]
  | cons key keys ih => simpa [maximum, List.toFinset_cons] using congrArg (max (value key)) ih

end SubtreeProofs.FiniteTable

end
