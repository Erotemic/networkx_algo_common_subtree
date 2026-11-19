module

public import SubtreeProofs.Complexity.EditDistance.Clients
public import SubtreeProofs.Complexity.Memo.RepresentationWork

/-! Both executable edit-distance representations consume the same generic
whole-run work theorem. The bounds include actual cache setup and dense index
encoding. They cover all declared event currencies, not input/list access,
body construction, bit complexity, persistent copying or source realization. -/

@[expose] public section

namespace SubtreeProofs.Complexity.EditDistance

variable {Symbol : Type} [DecidableEq Symbol]

open scoped BigOperators

def interior (left right : List Symbol) : Finset (Key left right) :=
  Finset.univ.filter fun key => key.1.val < left.length ∧ key.2.val < right.length

omit [DecidableEq Symbol] in
theorem interior_card (left right : List Symbol) :
    (interior left right).card = left.length * right.length := by
  rw [interior, ← Finset.univ_product_univ,
    Finset.filter_product (fun i : Fin (left.length + 1) => i.val < left.length)
      (fun j : Fin (right.length + 1) => j.val < right.length), Finset.card_product]
  simp only [Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_succ _)]

/-- Boundary states have no requests or local score operations. -/
def interiorCharge (left right : List Symbol) (units : Nat) (key : Key left right) : Nat :=
  if key.1.val < left.length ∧ key.2.val < right.length then units else 0

omit [DecidableEq Symbol] in
theorem interiorCharge_sum (left right : List Symbol) (units : Nat) :
    ∑ key : Key left right, interiorCharge left right units key =
      units * (left.length * right.length) := by
  unfold interiorCharge
  rw [← Finset.sum_filter]
  change (∑ _key ∈ interior left right, units) = _
  simp [interior_card, Nat.mul_comm]

theorem body_arity_charge (left right : List Symbol) (key : Key left right) :
    (Memo.Body.meaning (value left right) (body left right key)).requests.length =
      interiorCharge left right 3 key := by
  rw [body_requests]
  by_cases hl : key.1.val < left.length <;> by_cases hr : key.2.val < right.length <;>
    simp [interiorCharge, hl, hr]

theorem body_local_charge (left right : List Symbol) (key : Key left right) :
    (Memo.Body.meaning (value left right) (body left right key)).localWork =
      interiorCharge left right 5 key := by
  by_cases hl : key.1.val < left.length <;> by_cases hr : key.2.val < right.length <;>
    simp [body, interiorCharge, hl, hr]

theorem list_work_spec (left right : List Symbol) (roots : List (Key left right))
    (requestOverhead expansionOverhead : Nat) :
    let cells := (left.length + 1) * (right.length + 1)
    ∃ final, (runList left right roots).2 = .ok (roots.map (value left right)) final ∧
      Memo.TraceInvariant Memo.ListCache.ops (problem left right) [] final ∧
      (runList left right roots).1 + Memo.Event.totalWork requestOverhead expansionOverhead final.events ≤
        1 + (requestOverhead + cells) * (roots.length + 3 * cells) +
          (expansionOverhead + 6) * cells := by
  dsimp only
  obtain ⟨final, hr, ht, hw⟩ := Memo.roots_work_envelope Memo.ListCache.ops (problem left right)
    Memo.ListCache.workModel Finset.univ (fun _ => 3) 5 requestOverhead expansionOverhead
    (by simp) (fun key _ => body_request_bound left right (value left right) key)
    (fun key _ => body_local_bound left right (value left right) key)
    (left.length + right.length + 1) roots [] Memo.ListCache.initial_valid
    (Memo.ListCache.initial_sound (value left right))
    (fun key _ => rank_lt_total left right key) (by simp)
  refine ⟨final, hr, ht, ?_⟩
  simpa [Memo.ListCache.workModel, Memo.ListCache.ops, Fintype.card_prod,
    Nat.mul_comm, Nat.add_assoc] using Nat.add_le_add_left hw 1

theorem dense_work_spec (left right : List Symbol) (roots : List (Key left right))
    (requestOverhead expansionOverhead : Nat) :
    let cells := (left.length + 1) * (right.length + 1)
    ∃ final, (runDense left right roots).2 = .ok (roots.map (value left right)) final ∧
      Memo.TraceInvariant (Memo.DirectCache.productOps (left.length + 1) (right.length + 1) Nat)
        (problem left right) (Memo.DirectCache.buildEmpty Nat cells).1 final ∧
      (runDense left right roots).1 + Memo.Event.totalWork requestOverhead expansionOverhead final.events ≤
        cells + 1 + (requestOverhead + 3) * (roots.length + 3 * cells) +
          (expansionOverhead + 8) * cells := by
  dsimp only
  obtain ⟨final, hr, ht, hw⟩ := Memo.roots_work_envelope
    (Memo.DirectCache.productOps (left.length + 1) (right.length + 1) Nat) (problem left right)
    (Memo.DirectCache.productWorkModel (left.length + 1) (right.length + 1) Nat)
    Finset.univ (fun _ => 3) 5 requestOverhead expansionOverhead
    (by simp) (fun key _ => body_request_bound left right (value left right) key)
    (fun key _ => body_local_bound left right (value left right) key)
    (left.length + right.length + 1) roots
    (Memo.DirectCache.buildEmpty Nat ((left.length + 1) * (right.length + 1))).1
    (Memo.DirectCache.product_initial_valid _ _ Nat)
    (Memo.DirectCache.product_initial_sound _ _ Nat (value left right))
    (fun key _ => rank_lt_total left right key) (by simp)
  refine ⟨final, hr, ht, ?_⟩
  rw [dense_setup]
  simpa [Memo.DirectCache.productWorkModel, Memo.DirectCache.productOps, Memo.DirectCache.ops,
    Memo.DirectCache.buildEmpty_empty, Fintype.card_prod, Nat.mul_comm, Nat.add_assoc] using
    Nat.add_le_add_left hw ((left.length + 1) * (right.length + 1) + 1)

/-- Nonuniform charging preserves the zero work/request contribution of every
boundary body. Only `n*m` interior states contribute the three/five charges. -/
theorem list_weighted_work_spec (left right : List Symbol) (roots : List (Key left right))
    (requestOverhead expansionOverhead : Nat) :
    let cells := (left.length + 1) * (right.length + 1)
    let inner := left.length * right.length
    ∃ final, (runList left right roots).2 = .ok (roots.map (value left right)) final ∧
      Memo.TraceInvariant Memo.ListCache.ops (problem left right) [] final ∧
      (runList left right roots).1 + Memo.Event.totalWork requestOverhead expansionOverhead final.events ≤
        1 + (requestOverhead + cells) * (roots.length + 3 * inner) +
          (expansionOverhead + 1) * cells + 5 * inner := by
  dsimp only
  obtain ⟨final, hr, ht, hw⟩ := Memo.roots_weighted_work_envelope Memo.ListCache.ops (problem left right)
    Memo.ListCache.workModel Finset.univ (interiorCharge left right 3) (interiorCharge left right 5)
    requestOverhead expansionOverhead (by simp)
    (fun key _ => Nat.le_of_eq (body_arity_charge left right key))
    (fun key _ => Nat.le_of_eq (body_local_charge left right key))
    (left.length + right.length + 1) roots [] Memo.ListCache.initial_valid
    (Memo.ListCache.initial_sound (value left right))
    (fun key _ => rank_lt_total left right key) (by simp)
  refine ⟨final, hr, ht, ?_⟩
  simpa [Memo.ListCache.workModel, Memo.ListCache.ops, Fintype.card_prod,
    interiorCharge_sum, Nat.add_assoc] using Nat.add_le_add_left hw 1

theorem dense_weighted_work_spec (left right : List Symbol) (roots : List (Key left right))
    (requestOverhead expansionOverhead : Nat) :
    let cells := (left.length + 1) * (right.length + 1)
    let inner := left.length * right.length
    ∃ final, (runDense left right roots).2 = .ok (roots.map (value left right)) final ∧
      Memo.TraceInvariant (Memo.DirectCache.productOps (left.length + 1) (right.length + 1) Nat)
        (problem left right) (Memo.DirectCache.buildEmpty Nat cells).1 final ∧
      (runDense left right roots).1 + Memo.Event.totalWork requestOverhead expansionOverhead final.events ≤
        cells + 1 + (requestOverhead + 3) * (roots.length + 3 * inner) +
          (expansionOverhead + 3) * cells + 5 * inner := by
  dsimp only
  obtain ⟨final, hr, ht, hw⟩ := Memo.roots_weighted_work_envelope
    (Memo.DirectCache.productOps (left.length + 1) (right.length + 1) Nat) (problem left right)
    (Memo.DirectCache.productWorkModel (left.length + 1) (right.length + 1) Nat)
    Finset.univ (interiorCharge left right 3) (interiorCharge left right 5)
    requestOverhead expansionOverhead (by simp)
    (fun key _ => Nat.le_of_eq (body_arity_charge left right key))
    (fun key _ => Nat.le_of_eq (body_local_charge left right key))
    (left.length + right.length + 1) roots
    (Memo.DirectCache.buildEmpty Nat ((left.length + 1) * (right.length + 1))).1
    (Memo.DirectCache.product_initial_valid _ _ Nat)
    (Memo.DirectCache.product_initial_sound _ _ Nat (value left right))
    (fun key _ => rank_lt_total left right key) (by simp)
  refine ⟨final, hr, ht, ?_⟩
  rw [dense_setup]
  simpa [Memo.DirectCache.productWorkModel, Memo.DirectCache.productOps, Memo.DirectCache.ops,
    Memo.DirectCache.buildEmpty_empty, Fintype.card_prod, interiorCharge_sum, Nat.add_assoc] using
    Nat.add_le_add_left hw ((left.length + 1) * (right.length + 1) + 1)

end SubtreeProofs.Complexity.EditDistance
