module

public import SubtreeProofs.Rust.LookupOwnerTransfers
public import SubtreeProofs.Rust.LookupSpatialExecution
public import SubtreeProofs.Rust.SourceHeapHelperWorld

/-! Exact append-only helper ownership growth. Every newly allocated Box
occurs once in the output ledger, alongside every transferred old occurrence.
Guarded disposable clobbers retain all owners. No native depth premise is used. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Owners

open Spatial

def fresh (before after : Memory) : List Nat := List.range' before.length (after.length - before.length)

theorem fresh_compose {first middle last : Memory} (h₁ : Extends first middle) (h₂ : Extends middle last) :
    fresh first middle ++ fresh middle last = fresh first last := by
  have hlen₁ := h₁.length_le
  have hlen₂ := h₂.length_le
  have hs : first.length + (middle.length - first.length) = middle.length := by omega
  have hn : (middle.length - first.length) + (last.length - middle.length) = last.length - first.length := by omega
  simpa only [fresh, hs, hn] using
    (List.range'_append_1 (s := first.length) (m := middle.length - first.length) (n := last.length - middle.length))

structure Grows (before after : Memory) (input output : List Cell) : Prop where
  memory : Extends before after
  ledger : ∀ owners, FieldsFootprint before input owners →
    ∃ result, FieldsFootprint after output result ∧ result.Perm (owners ++ fresh before after)

theorem Grows.of_conserves {memory : Memory} {input output : List Cell} (h : Conserves memory input output) :
    Grows memory memory input output := by
  refine ⟨.refl _, ?_⟩
  intro owners ho
  obtain ⟨result, hr, hp⟩ := h owners ho
  exact ⟨result, hr, by simpa only [fresh, Nat.sub_self, List.range'_zero, List.append_nil] using hp⟩

theorem Grows.trans {first middle last : Memory} {input temporary output : List Cell}
    (h₁ : Grows first middle input temporary) (h₂ : Grows middle last temporary output) : Grows first last input output := by
  refine ⟨h₁.memory.trans h₂.memory, ?_⟩
  intro owners ho
  obtain ⟨a, ha, hp⟩ := h₁.ledger owners ho
  obtain ⟨b, hb, hq⟩ := h₂.ledger a ha
  refine ⟨b, hb, ?_⟩
  simpa only [List.append_assoc, fresh_compose h₁.memory h₂.memory] using
    hq.trans (hp.append_right (fresh middle last))

theorem Grows.frame {before after : Memory} {input output : List Cell} (h : Grows before after input output)
    (frame : List Cell) : Grows before after (input ++ frame) (output ++ frame) := by
  refine ⟨h.memory, ?_⟩
  intro owners ho
  obtain ⟨a, b, rfl, ha, hb⟩ := fieldsFootprint_split input ho
  obtain ⟨c, hc, hp⟩ := h.ledger a ha
  refine ⟨c ++ b, fieldsFootprint_append hc (fieldsFootprint_mono h.memory hb), ?_⟩
  have swap : ((a ++ fresh before after) ++ b).Perm ((a ++ b) ++ fresh before after) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := fresh before after) (l₂ := b)).append_left a
  exact (hp.append_right b).trans swap

def CallsGrow {F : Type} (argsMatch : F → List Cell → Prop) (call : CallsFor F) : Prop :=
  ∀ function cells memory cell after cost, argsMatch function cells →
    call function cells memory = some (cell, after, cost) → Grows memory after cells [cell]

def resultCells (count : Nat) : Result → List Cell
  | .next env => values count env
  | .returned cell => [cell]

theorem action_grows {F : Type} {argsMatch : F → List Cell → Prop}
    {calleeOutput : F → List Ty → Option Ty} {call : CallsFor F} {good : Frame.CallSafetyFor F}
    (hcall : CallsGrow argsMatch call) {memory after : Memory} {locals : List Ty} {env env' : Locals} {cost : Cost}
    (hb : Bounded locals.length env) (instruction : Action F)
    (ht : SourceTypes.ActionConstraintsWith calleeOutput locals instruction)
    (hg : Frame.ActionSafeWith argsMatch call good memory env instruction)
    (hr : Heap.action call memory env instruction = some (env', after, cost)) :
    Bounded locals.length env' ∧ Grows memory after (values locals.length env) (values locals.length env') := by
  cases instruction with
  | scope slot =>
    cases hr
    exact ⟨hb.clear slot, Grows.of_conserves (clear ht hg)⟩
  | dropMoved slot =>
    have hn : env slot = none := hg
    simp only [Heap.action, hn, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact ⟨hb, Grows.of_conserves (Conserves.refl _ _)⟩
  | assign slot rhs =>
    obtain ⟨ty, _, hd⟩ := ht
    have hs : slot < locals.length := List.getElem?_eq_some_iff.mp hd |>.choose
    cases hx : Heap.rvalue memory env rhs with
    | none => simp [Heap.action, hx] at hr
    | some pair =>
      rcases pair with ⟨cell, middle⟩
      simp only [Heap.action, hx, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨hb', hp⟩ := rvalue hb rhs hx
      exact ⟨hb'.store hs _, Grows.of_conserves (hp.trans (store hs (hg cell middle hx) cell))⟩
  | call function args slot =>
    obtain ⟨_, ty, _, _, hd⟩ := ht
    have hs : slot < locals.length := List.getElem?_eq_some_iff.mp hd |>.choose
    cases hx : Heap.operands memory args env with
    | none => simp [Heap.action, hx] at hr
    | some pair =>
      rcases pair with ⟨cells, middle⟩
      cases hy : call function cells memory with
      | none => simp [Heap.action, hx, hy] at hr
      | some pair =>
        rcases pair with ⟨cell, mem, inner⟩
        simp only [Heap.action, hx, hy, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨hb', hp⟩ := operands hb args hx
        have called := hcall function cells memory cell mem inner (hg cells middle hx).2.1 hy
        exact ⟨hb'.store hs _, (Grows.of_conserves hp).trans
          ((called.frame (values locals.length middle)).trans
            (Grows.of_conserves (store hs (hg cells middle hx).1 cell)))⟩

def ResultBounded (count : Nat) : Result → Prop
  | .next env => Bounded count env
  | .returned _ => True

theorem guarded_grows {F : Type} {argsMatch : F → List Cell → Prop}
    {calleeOutput : F → List Ty → Option Ty} {call : CallsFor F} {good : Frame.CallSafetyFor F}
    (hcall : CallsGrow argsMatch call) {code : Code F} {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (hg : Frame.GuardedWith argsMatch call good code memory env result after cost)
    {locals : List Ty} {output : Ty} (ht : SourceTypes.CodeConstraintsWith calleeOutput locals output code)
    (hb : Bounded locals.length env) :
    ResultBounded locals.length result ∧
      Grows memory after (values locals.length env) (resultCells locals.length result) := by
  induction hg generalizing locals output with
  | done => exact ⟨hb, Grows.of_conserves (Conserves.refl _ _)⟩
  | ret hr hd =>
    cases ht with
    | ret hret =>
      have hs : 0 < locals.length := List.getElem?_eq_some_iff.mp hret |>.choose
      exact ⟨trivial, Grows.of_conserves (returning hs hr hd)⟩
  | step ha hg hrest ih =>
    cases ht with
    | step hi ht =>
      obtain ⟨hb', hgrow⟩ := action_grows hcall hb _ hi hg ha
      obtain ⟨hb'', htail⟩ := ih ht hb'
      exact ⟨hb'', hgrow.trans htail⟩
  | branchReturned hscrut hsel harm ih =>
    cases ht with
    | branch hst hk ho hy hn hrest =>
      obtain ⟨hb', hp⟩ := scrutinee hb _ hscrut
      obtain ⟨hb'', htail⟩ := ih (selected_constraintsWith hy hn hsel) hb'
      exact ⟨hb'', (Grows.of_conserves hp).trans htail⟩
  | branchNext hscrut hsel harm hrest ihArm ihRest =>
    cases ht with
    | branch hst hk ho hy hn ht =>
      obtain ⟨hb', hp⟩ := scrutinee hb _ hscrut
      obtain ⟨hb'', harm⟩ := ihArm (selected_constraintsWith hy hn hsel) hb'
      obtain ⟨hb''', htail⟩ := ihRest ht hb''
      exact ⟨hb''', (Grows.of_conserves hp).trans (harm.trans htail)⟩

end SubtreeProofs.Rust.LookupSource.Heap.Owners
