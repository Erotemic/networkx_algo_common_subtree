module

public import SubtreeProofs.Rust.SourceEvalLegacyControl

/-! Source operations that do not observe a local preserve agreement outside
that local. Writes synchronize it; drops count as observations because their
complete destructor cost depends on the retained initialization mask. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LoanEnding

open LookupSource LookupSource.Partial

def Same (slot : Nat) (first second : State) : Prop := ∀ index, index ≠ slot → first index = second index

theorem Same.refl (slot : Nat) (state : State) : Same slot state state := fun _ _ => rfl

theorem Same.set {slot : Nat} {first second : State} (h : Same slot first second) (destination : Nat) (value : Slot) :
    Same slot (first.set destination value) (second.set destination value) := by
  intro index hn
  by_cases hi : index = destination <;> simp only [Locals.set, hi, ite_true, ite_false]
  exact h index hn

theorem Same.synchronize {slot : Nat} {first second : State} (h : Same slot first second) (value : Slot) :
    first.set slot value = second.set slot value := by
  funext index
  by_cases hi : index = slot <;> simp only [Locals.set, hi, ite_true, ite_false]
  exact h index hi

theorem Same.forget (state : State) (slot : Nat) : Same slot state (state.set slot .empty) := by
  intro index hn
  simp only [Locals.set, hn, ite_false]

def avoidsPlace (slot : Nat) (place : Place) : Bool := decide ((splitPlace place).1 ≠ slot)

def avoidsOperand (slot : Nat) : Operand → Bool
  | .move place | .copy place => avoidsPlace slot place
  | .boolean _ | .number _ => true

def avoidsOperands (slot : Nat) (args : List Operand) : Bool := args.all (avoidsOperand slot)

def avoidsExpr (slot : Nat) : Expr → Bool
  | .use op => avoidsOperand slot op
  | .address place => avoidsPlace slot place
  | .aggregate _ _ args => avoidsOperands slot args
  | .less first second => avoidsOperand slot first && avoidsOperand slot second

def avoidsAction (slot : Nat) : Action → Bool
  | .storageLive _ | .storageDead _ | .undefinedBehavior => true
  | .assign _ rhs => avoidsExpr slot rhs
  | .call _ args _ => avoidsOperands slot args
  | .drop destination => decide (destination ≠ slot)
  | .fakeRead place => avoidsPlace slot place

def writes : Action → Option Nat
  | .storageLive slot | .storageDead slot | .assign slot _ | .call _ _ slot | .drop slot => some slot
  | _ => none

def avoidsScrutinee (slot : Nat) : LookupSource.Scrutinee → Bool
  | .discriminant place => avoidsPlace slot place
  | .value (.move destination) => decide (destination ≠ slot)
  | .value (.copy place) => avoidsPlace slot place
  | .value (.boolean _) => true

def PacketRel {α : Type} (slot : Nat) (first second : α × State) : Prop :=
  first.1 = second.1 ∧ Same slot first.2 second.2

theorem rel_bind {α β γ δ : Type} {r : α → β → Prop} {s : γ → δ → Prop}
    {first : Option α} {second : Option β} {left : α → Option γ} {right : β → Option δ}
    (h : Option.Rel r first second) (next : ∀ a b, r a b → Option.Rel s (left a) (right b)) :
    Option.Rel s (first.bind left) (second.bind right) := by
  cases h with
  | none => exact .none
  | some h => exact next _ _ h

theorem rel_same {α : Type} (value : Option α) : Option.Rel Eq value value := by
  cases value with
  | none => exact .none
  | some value => exact .some rfl

theorem rel_eq {α : Type} {first second : Option α} (h : Option.Rel Eq first second) : first = second := by
  cases h with
  | none => rfl
  | some h => cases h; rfl

theorem read_congr {slot : Nat} {first second : State} (h : Same slot first second) (place : Place)
    (hn : avoidsPlace slot place = true) : first.read place = second.read place := by
  have he := h (splitPlace place).1 (of_decide_eq_true hn)
  simp only [Locals.read, he]

theorem operand_congr {slot : Nat} {first second : State} (h : Same slot first second) (op : Operand)
    (hn : avoidsOperand slot op = true) : Option.Rel (PacketRel slot) (operand first op) (operand second op) := by
  cases op with
  | move place =>
    have he := h (splitPlace place).1 (of_decide_eq_true hn)
    simp only [operand, Locals.move, he]
    cases ht : (second (splitPlace place).1).take (splitPlace place).2 with
    | none => exact .none
    | some pair =>
      rcases pair with ⟨value, remaining⟩
      exact .some ⟨rfl, h.set _ remaining⟩
  | copy place =>
    have he := read_congr h place hn
    simp only [operand, he]
    cases hr : second.read place with
    | none => exact .none
    | some value =>
      cases value with
      | boolean _ | reference _ => exact .some ⟨rfl, h⟩
      | number n => by_cases hb : n < 2^32 <;> simp only [hb, ite_true, ite_false, Bind.bind, Option.bind] <;> first | exact .none | exact .some ⟨rfl, h⟩
      | node _ _ _ | boxed _ => exact .none
  | boolean _ => exact .some ⟨rfl, h⟩
  | number n => by_cases hb : n < 2^32 <;> simp only [operand, hb, ite_true, ite_false] <;> first | exact .none | exact .some ⟨rfl, h⟩

theorem operands_congr {slot : Nat} {first second : State} (h : Same slot first second) (args : List Operand)
    (hn : avoidsOperands slot args = true) : Option.Rel (PacketRel slot) (operands first args) (operands second args) := by
  induction args generalizing first second with
  | nil => exact .some ⟨rfl, h⟩
  | cons op rest ih =>
    have hall := List.all_eq_true.mp hn
    simp only [operands]
    apply rel_bind (operand_congr h op (hall _ (by simp)))
    rintro ⟨value, middle⟩ ⟨other, current⟩ ⟨rfl, hm⟩
    apply rel_bind (ih hm (List.all_eq_true.mpr (fun _ hp => hall _ (List.mem_cons_of_mem _ hp))))
    rintro ⟨values, after⟩ ⟨others, final⟩ ⟨rfl, hs⟩
    exact .some ⟨rfl, hs⟩

theorem expression_congr {slot : Nat} {first second : State} (h : Same slot first second) (rhs : Expr)
    (hn : avoidsExpr slot rhs = true) : Option.Rel (PacketRel slot) (expression first rhs) (expression second rhs) := by
  cases rhs with
  | use op => exact operand_congr h op hn
  | address place =>
    have he := read_congr h place hn
    simp only [expression, he]
    cases hr : second.read place with
    | none => exact .none
    | some value => exact .some ⟨rfl, h⟩
  | aggregate kind tag args =>
    simp only [expression]
    apply rel_bind (operands_congr h args hn)
    rintro ⟨values, after⟩ ⟨others, final⟩ ⟨rfl, hs⟩
    exact .some ⟨rfl, hs⟩
  | less left right =>
    have hh := Bool.and_eq_true_iff.mp hn
    simp only [expression]
    apply rel_bind (operand_congr h left hh.1)
    rintro ⟨value, middle⟩ ⟨other, current⟩ ⟨rfl, hm⟩
    apply rel_bind (operand_congr hm right hh.2)
    rintro ⟨value', after⟩ ⟨other', final⟩ ⟨rfl, hs⟩
    cases value <;> cases value' <;> try exact .none
    rename_i left right
    dsimp only
    cases hc : less32 left right with
    | none => simp only [Bind.bind, Option.bind]; exact .none
    | some answer => simp only [Bind.bind, Option.bind]; exact .some ⟨rfl, hs⟩

def StepRel (slot : Nat) (act : Action) (first second : State × Cost) : Prop :=
  Same slot first.1 second.1 ∧ first.2 = second.2 ∧ (writes act = some slot → first.1 = second.1)

theorem action_congr {slot : Nat} {first second : State} (h : Same slot first second) (call : Calls) (act : Action)
    (hn : avoidsAction slot act = true) : Option.Rel (StepRel slot act) (action call first act) (action call second act) := by
  cases act with
  | storageLive destination | storageDead destination =>
    all_goals
      refine .some ⟨h.set destination .empty, rfl, ?_⟩
      intro he
      have hi := Option.some.inj he
      subst destination
      exact h.synchronize .empty
  | assign destination rhs =>
    simp only [action]
    apply rel_bind (expression_congr h rhs hn)
    rintro ⟨value, after⟩ ⟨other, final⟩ ⟨rfl, hs⟩
    refine .some ⟨hs.set destination _, rfl, ?_⟩
    intro he
    have hi := Option.some.inj he
    subst destination
    exact hs.synchronize _
  | call function args destination =>
    simp only [action]
    apply rel_bind (operands_congr h args hn)
    rintro ⟨values, after⟩ ⟨others, final⟩ ⟨rfl, hs⟩
    cases hr : call function values with
    | none => exact .none
    | some pair =>
      rcases pair with ⟨value, cost⟩
      refine .some ⟨hs.set destination _, rfl, ?_⟩
      intro he
      have hi := Option.some.inj he
      subst destination
      exact hs.synchronize _
  | drop destination =>
    have he := h destination (of_decide_eq_true hn)
    exact .some ⟨h.set destination .empty, by change Cost.local _ (first destination).dropWork = Cost.local _ (second destination).dropWork; rw [he], fun hw =>
      False.elim ((of_decide_eq_true hn) (Option.some.inj hw))⟩
  | fakeRead _ => exact .some ⟨h, rfl, by intro he; cases he⟩
  | undefinedBehavior => exact .none

theorem boolean_congr {slot : Nat} {first second : Option (Value × State)} (h : Option.Rel (PacketRel slot) first second) :
    Option.Rel (PacketRel slot)
      (first.bind (fun (value, after) => match value with | .boolean b => some (Key.boolean b, after) | _ => none))
      (second.bind (fun (value, after) => match value with | .boolean b => some (Key.boolean b, after) | _ => none)) := by
  apply rel_bind h
  rintro ⟨value, after⟩ ⟨other, final⟩ ⟨rfl, hs⟩
  cases value <;> first | exact .none | exact .some ⟨rfl, hs⟩

theorem scrutinee_congr {slot : Nat} {first second : State} (h : Same slot first second) (scrut : LookupSource.Scrutinee)
    (hn : avoidsScrutinee slot scrut = true) :
    Option.Rel (PacketRel slot) (SourceEval.scrutinee first scrut) (SourceEval.scrutinee second scrut) := by
  cases scrut with
  | discriminant place =>
    have he := h (splitPlace place).1 (of_decide_eq_true (show avoidsPlace slot place = true from hn))
    simp only [SourceEval.scrutinee, he]
    cases hr : (second (splitPlace place).1).get (splitPlace place).2 with
    | none => exact .none
    | some part => cases part <;> first | exact .none | exact .some ⟨rfl, h⟩
  | value op =>
    cases op with
    | move destination => exact boolean_congr (operand_congr h (.move (.local destination)) hn)
    | copy place => exact boolean_congr (operand_congr h (.copy place) hn)
    | boolean b => exact boolean_congr (operand_congr h (.boolean b) hn)

end SubtreeProofs.Rust.SourceEval.LoanEnding
