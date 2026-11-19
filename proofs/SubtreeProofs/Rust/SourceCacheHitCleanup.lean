module

public import SubtreeProofs.Rust.SourceCacheHitTransfer
public import SubtreeProofs.Rust.SourceQueryRetirement

/-! Construct every real cache-hit destructor and storage retirement after the
return tuple has been assembled. No owned table cell is destroyed. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def hitCleanupRoots (roots : Roots) : Roots :=
  ((((roots.set 12 none).set 10 none).set 9 none).set 6 none).set 4 none

theorem hit_cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {root4 root6 root9 root10 root12 : Binding}
    (bound4 : active.roots 4 = some root4) (bound6 : active.roots 6 = some root6)
    (bound9 : active.roots 9 = some root9) (bound10 : active.roots 10 = some root10)
    (bound12 : active.roots 12 = some root12)
    (empty3 : active.state 3 = .empty) (hole4 : active.state 4 = .node .optional 1 [.empty])
    (empty6 : active.state 6 = .empty) (empty9 : active.state 9 = .empty)
    (empty10 : active.state 10 = .empty) (empty12 : active.state 12 = .empty)
    {result : Option CommonEmbedding} {table : MemoTable}
    (output : active.state 0 = Slot.ofValue (encodeOutput result table)) :
    ∃ final after, Calling.Prefix callee callers .done (hitActions.drop 11) world active final after ∧
      QueryMachine before callers previous external final after ∧
      after.roots = hitCleanupRoots active.roots ∧ after.count = active.count ∧
      after.state 0 = Slot.ofValue (encodeOutput result table) ∧ after.state 3 = .empty := by
  have plan : RetirementPlan active.roots (hitActions.drop 11) (hitCleanupRoots active.roots) := by
    refine .drop bound12 (.dead bound12 (.drop (binding := root10) ?_ (.dead (binding := root10) ?_ (.drop (binding := root9) ?_ (.dead (binding := root9) ?_ (.drop (binding := root4) ?_ (.dead (binding := root6) ?_ (.dead (binding := root4) ?_ (.nil _)))))))))
    all_goals simp only [Roots.set, show (10 : Nat) ≠ 12 by decide, show (9 : Nat) ≠ 12 by decide,
      show (9 : Nat) ≠ 10 by decide, show (4 : Nat) ≠ 12 by decide, show (4 : Nat) ≠ 10 by decide,
      show (4 : Nat) ≠ 9 by decide, show (6 : Nat) ≠ 12 by decide, show (6 : Nat) ≠ 10 by decide,
      show (6 : Nat) ≠ 9 by decide, show (4 : Nat) ≠ 6 by decide, ite_false]
    all_goals assumption
  have zero : ZeroRetirement (hitActions.drop 11) active.state := by
    intro slot member
    simp only [hitActions, List.drop, List.mem_cons, List.not_mem_nil, or_false, Action.drop.injEq,
      Action.storageDead.injEq, reduceCtorEq, false_or] at member
    rcases member with member | member
    · rcases member with rfl | rfl | rfl | rfl
      · rw [empty12]; decide +kernel
      · rw [empty10]; decide +kernel
      · rw [empty9]; decide +kernel
      · rw [hole4]; decide +kernel
    · rcases member with rfl | rfl | rfl | rfl | rfl
      · rw [empty12]; decide +kernel
      · rw [empty10]; decide +kernel
      · rw [empty9]; decide +kernel
      · rw [empty6]; decide +kernel
      · rw [hole4]; decide +kernel
  obtain ⟨final, after, run, machine, roots, count⟩ := plan.complete callee .done h rfl zero
  refine ⟨final, after, run, machine, roots, count, ?_, ?_⟩
  · exact (run.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [output]; exact ofValue_typed (encodeOutput_typed result table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel) (by decide +kernel)).trans output
  · exact (run.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [empty3]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty3

end SubtreeProofs.Rust.SourceEval.Evaluator
