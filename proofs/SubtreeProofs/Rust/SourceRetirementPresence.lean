module

public import SubtreeProofs.Rust.SourceRootPresence
public import SubtreeProofs.Rust.SourceOriginalRetirement

/-! A finite storage-presence check constructs a retirement plan using actual
bindings. It does not assume the desired post-frame or invent root addresses. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def retirementReady (present : Nat → Bool) : List Action → Bool
  | [] => true
  | .drop slot :: rest => present slot && retirementReady present rest
  | .storageDead slot :: rest => present slot && retirementReady (rootPresenceStep present (.storageDead slot)) rest
  | _ :: _ => false

def retirementRoots (roots : Roots) : List Action → Roots
  | [] => roots
  | .storageDead slot :: rest => retirementRoots (roots.set slot none) rest
  | _ :: rest => retirementRoots roots rest

theorem RetirementPlan.of_presence {roots : Roots} {actions : List Action}
    (ready : retirementReady (rootPresence roots) actions = true) :
    RetirementPlan roots actions (retirementRoots roots actions) := by
  induction actions generalizing roots with
  | nil => exact .nil _
  | cons act rest ih =>
    cases act <;> try cases ready
    case drop slot =>
      obtain ⟨bound, next⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨binding, root⟩ := Option.isSome_iff_exists.mp bound
      exact .drop root (ih next)
    case storageDead slot =>
      obtain ⟨bound, next⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨binding, root⟩ := Option.isSome_iff_exists.mp bound
      have present : rootPresence (roots.set slot none) = rootPresenceStep (rootPresence roots) (.storageDead slot) := by
        funext index
        simp only [rootPresence, rootPresenceStep, Roots.set]
        split <;> rfl
      exact .dead root (ih (by rw [present]; exact next))

theorem rootPresence.bound {roots : Roots} {present : Nat → Bool}
    (same : rootPresence roots = present) {slot : Nat} (live : present slot = true) :
    ∃ binding, roots slot = some binding := by
  exact Option.isSome_iff_exists.mp (by change rootPresence roots slot = true; rw [same]; exact live)

end SubtreeProofs.Rust.SourceEval.Addressed
