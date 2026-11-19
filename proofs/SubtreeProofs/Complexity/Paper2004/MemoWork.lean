module

public import SubtreeProofs.Complexity.Paper2004.MemoCorrespondence
public import SubtreeProofs.Complexity.Memo.RepresentationWork

/-! LV whole-run bounds in the declared numerical-interpreter currencies.
The maintained evaluator's exact values/tables/counters already correspond.
Whole-key tests, score operations and conses here do not yet price structural
words, key/body construction, witness materialization or source execution. -/

@[expose] public section

namespace SubtreeProofs.Complexity.Paper2004

open SubtreeProofs.Paper2004.OrderedTree
open SubtreeProofs.Complexity.Memo

theorem roots_list_work (left right : DyckWord) (table : MemoTable) (roots : List MemoKey)
    (requestOverhead expansionOverhead : Nat)
    (hv : (table.map Prod.fst).Nodup) (hs : MemoSound table)
    (hroots : ∀ key ∈ roots, key ∈ envelope left right) :
    let missing := (envelope left right).filter fun key => (memoLookup key table).isNone
    ∃ final, evalRoots listOps body (left.semilength + right.semilength + 1) roots
        ⟨table, []⟩ = .ok (roots.map score) final ∧
      TraceInvariant listOps problem table final ∧
      Event.totalWork requestOverhead expansionOverhead final.events ≤
        (requestOverhead + table.length + missing.card) * (roots.length + 4 * missing.card) +
          (expansionOverhead + 5) * missing.card := by
  simpa [problem, ListCache.workModel, contents_eq_memoLookup, Nat.mul_comm, Nat.add_assoc]
    using roots_work_envelope listOps problem ListCache.workModel (envelope left right)
      (fun _ => 4) 4 requestOverhead expansionOverhead (envelope_closed left right)
      (fun key _ => body_request_bound score key.1 key.2)
      (fun key _ => body_local_bound score key.1 key.2)
      (left.semilength + right.semilength + 1) roots table hv (sound_of_memoSound table hs)
      (fun key hk => envelope_rank_lt left right key (hroots key hk)) hroots

/-- Cache setup is an executed operation even when the root list is empty. -/
def runList (left right : DyckWord) (roots : List MemoKey) :
    Nat × EStateM.Result Unit (EvalState MemoKey MemoTable) (List Nat) :=
  let initial := (ListCache.buildEmpty : MemoTable × Nat)
  (initial.2, evalRoots listOps body (left.semilength + right.semilength + 1)
    roots ⟨initial.1, []⟩)

theorem cold_list_work (left right : DyckWord) (roots : List MemoKey)
    (requestOverhead expansionOverhead : Nat)
    (hroots : ∀ key ∈ roots, key ∈ envelope left right) :
    let cells := (envelope left right).card
    ∃ final, (runList left right roots).2 = .ok (roots.map score) final ∧
      TraceInvariant listOps problem [] final ∧
      (runList left right roots).1 + Event.totalWork requestOverhead expansionOverhead final.events ≤
        1 + (requestOverhead + cells) * (roots.length + 4 * cells) +
          (expansionOverhead + 5) * cells := by
  obtain ⟨final, hr, ht, hw⟩ := roots_list_work left right [] roots requestOverhead expansionOverhead
    (by simp) (by intro _ hm; simp at hm) hroots
  refine ⟨final, hr, ht, ?_⟩
  simpa [runList, ListCache.buildEmpty, memoLookup, Nat.add_assoc] using Nat.add_le_add_left hw 1

end SubtreeProofs.Complexity.Paper2004
