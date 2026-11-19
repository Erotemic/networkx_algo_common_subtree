module

public import SubtreeProofs.Rust.SourceEvalLoanEndings
public import SubtreeProofs.Rust.SourceActivationInventory

/-! Ending an unused shared-reference view retains stored pointer bits, stack
roots, classes and storage liveness. Only active read/loan metadata is forgotten;
the independent source masks are related by the complete source equivalence. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open SourceEval

theorem Frame.forget_shared {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) {value : LookupSource.Value} (hs : state slot = .shared value) :
    Frame world frame roots (state.set slot .empty) guards := by
  refine ⟨h.alive, ?_⟩
  intro index
  by_cases he : index = slot
  · subst index
    cases hr : roots slot with
    | none =>
      have hempty : state slot = .empty := by simpa only [hr] using h.slots slot
      rw [hs] at hempty
      cases hempty
    | some binding =>
      simp only [Partial.Locals.set, ite_true]
      obtain ⟨cell, used, hc, ht, _, hu⟩ := h.get hr
      exact ⟨cell, [], hc, ht, PartialGraph.empty cell, fun a hm => hu (List.mem_append_right _ hm)⟩
  · simpa only [Partial.Locals.set, he, ite_false] using h.slots index

theorem Frame.forget {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (code : SourceEval.Code) (slots : List Nat) :
    Frame world frame roots (LoanEnding.forget code slots state) guards := by
  induction slots generalizing state with
  | nil => exact h
  | cons slot rest ih =>
    simp only [LoanEnding.forget_cons]
    cases hs : state slot <;> try exact ih h
    by_cases he : LoanEnding.endsBeforeObservation slot code = true
    · simp only [he, ite_true]
      exact ih (h.forget_shared hs)
    · simp only [he, Bool.false_eq_true, ite_false]
      exact ih h

def Activation.forgetRefs (active : Activation) (code : SourceEval.Code) : Activation :=
  let prepared := LoanEnding.prepare code (List.range active.count) active.state
  { active with state := prepared.state }

theorem Activation.forgetRefs_valid {active : Activation} {world : World} (h : active.Valid world) (code : SourceEval.Code) :
    (active.forgetRefs code).Valid world := by
  obtain ⟨bound, guards, hf⟩ := h
  exact ⟨bound, guards, hf.forget code _⟩

theorem Activation.forgetRefs_source (active : Activation) (code : SourceEval.Code) (call : Calls) :
    SourceEval.exec call code (active.forgetRefs code).state = SourceEval.exec call code active.state :=
  LoanEnding.forget_source call code _ _

theorem Activation.forgetRefs_identity (active : Activation) (code : SourceEval.Code) :
    (active.forgetRefs code).frame = active.frame ∧ (active.forgetRefs code).count = active.count ∧
      (active.forgetRefs code).roots = active.roots := ⟨rfl, rfl, rfl⟩

theorem Activation.forgetRefs_boxes (active : Activation) (code : SourceEval.Code) (slot : Nat) :
    ((active.forgetRefs code).state slot).dropWork.boxes = (active.state slot).dropWork.boxes :=
  LoanEnding.forget_boxes code _ _ slot

theorem Activation.forgetRefs_observed (active : Activation) (code : SourceEval.Code) (slot : Nat)
    (hn : LoanEnding.endsBeforeObservation slot code = false) :
    (active.forgetRefs code).state slot = active.state slot :=
  LoanEnding.forget_observed code _ _ slot hn

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage
