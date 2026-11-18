module

public import SubtreeProofs.Rust.SourceRawMaskPreservation
public import SubtreeProofs.Rust.SourceCallingPrefixes
public import SubtreeProofs.Rust.SourcePrefixUnshared

/-! Untouched query masks survive actual prefixes containing calls. Reference
preparation is handled by real continuation observations or an unshared mask.
Prefix determinism identifies independently constructed stable checkpoints. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LocalPreservation

open LookupSource Partial

theorem action_no_write (index : Nat) {act : Action} (safe : action index act = true) :
    LoanEnding.writes act ≠ some index := by
  cases act with
  | storageLive destination | storageDead destination | drop destination =>
    intro same
    exact (of_decide_eq_true safe) (Option.some.inj same).symm
  | assign destination rhs | call function args destination =>
    intro same
    exact (of_decide_eq_true (Bool.and_eq_true_iff.mp safe).1) (Option.some.inj same).symm
  | fakeRead place | undefinedBehavior => simp [LoanEnding.writes]

end SubtreeProofs.Rust.SourceEval.LocalPreservation

namespace SubtreeProofs.Rust.SourceEval.LoanEnding

open LookupSource Partial

theorem unwritten_prefix_observed (index : Nat) (actions : List Action) (suffix : Code)
    (unchanged : ∀ act ∈ actions, writes act ≠ some index) (observed : endsBeforeObservation index suffix = false) :
    endsBeforeObservation index (actions.foldr Control.Tree.step suffix) = false := by
  induction actions with
  | nil => exact observed
  | cons act rest ih =>
    have next := ih (fun action member => unchanged action (List.mem_cons_of_mem act member))
    simp only [List.foldr_cons, endsBeforeObservation, unchanged act (by simp), decide_false, Bool.false_or, next, Bool.and_false]

end SubtreeProofs.Rust.SourceEval.LoanEnding

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.unshared_local_same_calls {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after)
    {index : Nat} (unshared : ∀ value, active.state index ≠ .shared value)
    (unchanged : actions.all (LocalPreservation.action index) = true) : after.state index = active.state index := by
  induction h with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    let code := (act :: rest).foldr Control.Tree.step suffix
    let prepared := active.forgetRefs code
    have preparedSame : prepared.state index = active.state index := LoanEnding.forget_unshared _ _ unshared
    have all := List.all_eq_true.mp unchanged
    have firstSame := (instruction_local_same index (all act (by simp)) run).trans preparedSame
    have currentUnshared : ∀ value, current.state index ≠ .shared value := by rw [firstSame]; exact unshared
    exact (ih currentUnshared (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem act member)))).trans firstSame

theorem Prefix.closed_local_same_calls {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after) {index : Nat} {ty : Ty}
    (typed : SlotTyped (active.state index) ty) (closed : Borrow.Closed ty)
    (unchanged : actions.all (LocalPreservation.action index) = true) : after.state index = active.state index := by
  induction h with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    let code := (act :: rest).foldr Control.Tree.step suffix
    let prepared := active.forgetRefs code
    have preparedSame : prepared.state index = active.state index := LoanEnding.forget_closed _ _ typed closed
    have all := List.all_eq_true.mp unchanged
    have firstSame := (instruction_local_same index (all act (by simp)) run).trans preparedSame
    have currentTyped : SlotTyped (current.state index) ty := by rw [firstSame]; exact typed
    exact (ih currentTyped (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem act member)))).trans firstSame

theorem Prefix.observed_local_same_calls {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after)
    {index : Nat} (observed : ∀ offset, offset < actions.length →
      LoanEnding.endsBeforeObservation index ((actions.drop offset).foldr Control.Tree.step suffix) = false)
    (unchanged : actions.all (LocalPreservation.action index) = true) : after.state index = active.state index := by
  induction h with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    let code := (act :: rest).foldr Control.Tree.step suffix
    let prepared := active.forgetRefs code
    have observedNow : LoanEnding.endsBeforeObservation index code = false := by simpa only [List.drop_zero] using observed 0 (by simp)
    have preparedSame : prepared.state index = active.state index := Activation.forgetRefs_observed active code index observedNow
    have all := List.all_eq_true.mp unchanged
    have firstSame := (instruction_local_same index (all act (by simp)) run).trans preparedSame
    have restObserved : ∀ offset, offset < rest.length →
        LoanEnding.endsBeforeObservation index ((rest.drop offset).foldr Control.Tree.step suffix) = false := by
      intro offset bound
      simpa only [List.drop_succ_cons] using observed (offset + 1) (by simp only [List.length_cons]; omega)
    exact (ih restObserved (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem act member)))).trans firstSame

theorem Prefix.retained_local_same_calls {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after) {index : Nat}
    (observed : LoanEnding.endsBeforeObservation index suffix = false)
    (unchanged : actions.all (LocalPreservation.action index) = true) : after.state index = active.state index := by
  induction h with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    let code := (act :: rest).foldr Control.Tree.step suffix
    let prepared := active.forgetRefs code
    have all := List.all_eq_true.mp unchanged
    have observedNow := LoanEnding.unwritten_prefix_observed index (act :: rest) suffix
      (fun action member => LocalPreservation.action_no_write index (all action member)) observed
    have preparedSame : prepared.state index = active.state index := Activation.forgetRefs_observed active code index observedNow
    have firstSame := (instruction_local_same index (all act (by simp)) run).trans preparedSame
    exact (ih (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem act member)))).trans firstSame

theorem Prefix.deterministic {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final otherFinal : World} {active after otherAfter : Activation}
    (h : Prefix callee callers suffix actions world active final after)
    (other : Prefix callee callers suffix actions world active otherFinal otherAfter) : final = otherFinal ∧ after = otherAfter := by
  induction h generalizing otherFinal otherAfter with
  | nil => cases other; exact ⟨rfl, rfl⟩
  | @cons world middle final active current after act rest cost run tail ih =>
    cases other with
    | cons runOther tailOther =>
      have same := (Prod.mk.inj (Option.some.inj (run.symm.trans runOther))).1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ih tailOther

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
