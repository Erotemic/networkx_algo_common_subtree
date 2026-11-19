module

public import SubtreeProofs.Rust.SourcePairHeadScopeEntry
public import SubtreeProofs.Rust.SourceFailurePacking
public import SubtreeProofs.Rust.SourceOriginalReturn

/-! Execute the actual input cleanup after a failed head request. The updated
table has moved into output zero; all remaining head locals have zero Box
owners and retire through the original bounded query-loan family. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def headCleanupActions : List Action :=
  [.storageDead 37, .drop 32, .storageDead 32, .drop 31, .storageDead 31,
   .storageDead 30, .storageDead 29, .storageDead 28, .storageDead 27, .storageDead 13]

def headCleanupRoots (roots : Roots) : Roots :=
  ((((((((roots.set 37 none).set 32 none).set 31 none).set 30 none).set 29 none).set 28 none).set 27 none).set 13 none)

theorem cleanupInputs_actions : cleanupInputs = headCleanupActions.foldr Control.Tree.step .done := rfl

theorem head_failure_cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    (bound : ∀ slot ∈ [13, 27, 28, 29, 30, 31, 32, 37], ∃ binding, active.roots slot = some binding)
    (none31 : active.state 31 = Slot.ofValue (encodeOption none)) (empty32 : active.state 32 = .empty)
    (empty37 : active.state 37 = .empty) (empty3 : active.state 3 = .empty)
    {table : MemoTable} (output : active.state 0 = Slot.ofValue (encodeOutput none table)) :
    ∃ final after,
      Calling.Prefix callee callers .done headCleanupActions world active final after ∧
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = headCleanupRoots active.roots ∧ after.count = active.count ∧
      after.state 0 = Slot.ofValue (encodeOutput none table) ∧ after.state 3 = .empty := by
  obtain ⟨root37, bound37⟩ := bound 37 (by simp)
  obtain ⟨root32, bound32⟩ := bound 32 (by simp)
  obtain ⟨root31, bound31⟩ := bound 31 (by simp)
  obtain ⟨root30, bound30⟩ := bound 30 (by simp)
  obtain ⟨root29, bound29⟩ := bound 29 (by simp)
  obtain ⟨root28, bound28⟩ := bound 28 (by simp)
  obtain ⟨root27, bound27⟩ := bound 27 (by simp)
  obtain ⟨root13, bound13⟩ := bound 13 (by simp)
  have plan : RetirementPlan active.roots headCleanupActions (headCleanupRoots active.roots) := by
    refine .dead bound37 (.drop (binding := root32) ?_ (.dead (binding := root32) ?_
      (.drop (binding := root31) ?_ (.dead (binding := root31) ?_ (.dead (binding := root30) ?_
        (.dead (binding := root29) ?_ (.dead (binding := root28) ?_ (.dead (binding := root27) ?_
          (.dead (binding := root13) ?_ (.nil _))))))))))
    all_goals first
      | simpa [Roots.set] using bound32
      | simpa [Roots.set] using bound31
      | simpa [Roots.set] using bound30
      | simpa [Roots.set] using bound29
      | simpa [Roots.set] using bound28
      | simpa [Roots.set] using bound27
      | simpa [Roots.set] using bound13
  have zero : ZeroRetirement headCleanupActions active.state := by
    intro slot member
    have selected : slot ∈ [13, 27, 28, 29, 30, 31, 32, 37] := by
      simp [headCleanupActions] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
    rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.zero 13 (by simp)
    · exact h.zero 27 (by simp)
    · exact h.zero 28 (by simp)
    · exact h.zero 29 (by simp)
    · exact h.zero 30 (by simp)
    · rw [none31]; simp [encodeOption, Slot.ofValue, Slot.dropWork, ofFields, dropFields]
    · rw [empty32]; simp only [Slot.dropWork]
    · rw [empty37]; simp only [Slot.dropWork]
  obtain ⟨final, after, steps, machine, roots, count, memory⟩ := plan.complete_original callee .done h rfl zero
  refine ⟨final, after, steps, machine, roots, count, ?_, ?_⟩
  · exact (steps.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [output]; exact ofValue_typed (encodeOutput_typed none table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel) (by decide +kernel)).trans output
  · exact (steps.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [empty3]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty3

end SubtreeProofs.Rust.SourceEval.Evaluator
