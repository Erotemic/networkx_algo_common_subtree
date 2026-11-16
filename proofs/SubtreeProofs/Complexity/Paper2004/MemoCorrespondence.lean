module

public import SubtreeProofs.Complexity.Paper2004.MemoBody
public import SubtreeProofs.Complexity.Memo.Bounds
public import SubtreeProofs.Complexity.Memo.Representations

/-! Exact operational correspondence with the maintained numerical evaluator.
This covers values, full association-list storage and all its existing counters,
including arbitrary warm tables. It is not a Rust/source runtime theorem. -/

@[expose] public section

namespace SubtreeProofs.Complexity.Paper2004

open SubtreeProofs.Paper2004
open SubtreeProofs.Paper2004.OrderedTree
open SubtreeProofs.Complexity.Memo

abbrev listOps : CacheOps MemoKey Nat MemoTable := ListCache.ops

theorem read_eq_memoFind (key : MemoKey) (table : MemoTable) :
    listOps.read key table = memoFind key table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨stored, value⟩
    change ListCache.read key ((stored, value) :: rest) = _
    simp only [ListCache.read, memoFind]
    change ListCache.read key rest = memoFind key rest at ih
    split
    · rfl
    · rw [ih]

theorem contents_eq_memoLookup (key : MemoKey) (table : MemoTable) :
    listOps.contents table key = memoLookup key table := by
  calc
    _ = (listOps.read key table).1 := (ListCache.read_value key table).symm
    _ = (memoFind key table).1 := congrArg Prod.fst (read_eq_memoFind key table)
    _ = _ := memoFind_value key table

/-- Strong execution correspondence: soundness and distinctness are unnecessary
for this operational equality, even though value/once-only theorems need them. -/
theorem eval_refines_memoLcs (fuel : Nat) (left right : DyckWord)
    (state : EvalState MemoKey MemoTable)
    (hbound : left.semilength + right.semilength < fuel) :
    ∃ final, eval listOps body fuel (left, right) state =
        .ok (memoLcs left right state.cache).value final ∧
      final.cache = (memoLcs left right state.cache).table ∧
      Event.calls final.events = Event.calls state.events + (memoLcs left right state.cache).calls ∧
      (Event.completedKeys final.events).length =
        (Event.completedKeys state.events).length + (memoLcs left right state.cache).misses ∧
      Event.lookupWork final.events =
        Event.lookupWork state.events + (memoLcs left right state.cache).comparisons := by
  induction fuel generalizing left right state with
  | zero => omega
  | succ fuel ih =>
    cases hread : (memoFind (left, right) state.cache).1 with
    | some value =>
      have hold : memoLcs left right state.cache =
          ⟨value, state.cache, 1, 0, (memoFind (left, right) state.cache).2⟩ := by
        rw [memoLcs]
        simp only [hread]
      rw [hold]
      refine ⟨recordLookup (left, right) (memoFind (left, right) state.cache).2 state, ?_, ?_⟩
      · rw [eval, read_eq_memoFind]
        simp only [hread]
      · simp [recordLookup, Event.calls, Event.completedKeys, Event.lookupWork, Nat.add_comm]
    | none =>
      let queried := recordLookup (left, right) (memoFind (left, right) state.cache).2 state
      by_cases hl : left = 0
      · have hold : memoLcs left right state.cache =
            ⟨0, ((left, right), 0) :: state.cache, 1, 1, (memoFind (left, right) state.cache).2⟩ := by
          rw [memoLcs]
          simp only [hread]
          simp only [hl, dite_true]
        rw [hold]
        refine ⟨recordComplete listOps (left, right) ⟨0, [], 0⟩ queried, ?_, ?_⟩
        · rw [eval, read_eq_memoFind]
          simp only [hread]
          simp [body, hl, Body.run, pure, EStateM.pure, queried]
        · simp [recordComplete, queried, recordLookup, listOps, ListCache.ops,
            Event.calls, Event.completedKeys, Event.lookupWork, Nat.add_comm]
      · by_cases hr : right = 0
        · have hold : memoLcs left right state.cache =
              ⟨0, ((left, right), 0) :: state.cache, 1, 1, (memoFind (left, right) state.cache).2⟩ := by
            rw [memoLcs]
            simp only [hread]
            simp only [hl, hr, dite_false, dite_true]
          rw [hold]
          refine ⟨recordComplete listOps (left, right) ⟨0, [], 0⟩ queried, ?_, ?_⟩
          · rw [eval, read_eq_memoFind]
            simp only [hread]
            simp [body, hl, hr, Body.run, pure, EStateM.pure, queried]
          · simp [recordComplete, queried, recordLookup, listOps, ListCache.ops,
              Event.calls, Event.completedKeys, Event.lookupWork, Nat.add_comm]
        · have hleft := BalancedDecomposition.contracted_semilength hl
          have hright := BalancedDecomposition.contracted_semilength hr
          simp only [DyckWord.semilength_add] at hleft hright
          obtain ⟨heads, hh, hhc, hhq, hhm, hhw⟩ :=
            ih left.insidePart right.insidePart queried (by omega)
          obtain ⟨tails, ht, htc, htq, htm, htw⟩ :=
            ih left.outsidePart right.outsidePart heads (by omega)
          obtain ⟨dropLeft, hdl, hdlc, hdlq, hdlm, hdlw⟩ :=
            ih (left.insidePart + left.outsidePart) right tails (by
              simp only [DyckWord.semilength_add]; omega)
          obtain ⟨dropRight, hdr, hdrc, hdrq, hdrm, hdrw⟩ :=
            ih left (right.insidePart + right.outsidePart) dropLeft (by
              simp only [DyckWord.semilength_add]; omega)
          let headRun := memoLcs left.insidePart right.insidePart queried.cache
          let tailRun := memoLcs left.outsidePart right.outsidePart heads.cache
          let leftRun := memoLcs (left.insidePart + left.outsidePart) right tails.cache
          let rightRun := memoLcs left (right.insidePart + right.outsidePart) dropLeft.cache
          let result : BodyResult MemoKey Nat :=
            ⟨max (max (headRun.value + tailRun.value + 1) leftRun.value) rightRun.value,
              [(left.insidePart, right.insidePart), (left.outsidePart, right.outsidePart),
                (left.insidePart + left.outsidePart, right),
                (left, right.insidePart + right.outsidePart)], 4⟩
          have hold : memoLcs left right state.cache =
              ⟨result.value, ((left, right), result.value) :: dropRight.cache,
                headRun.calls + tailRun.calls + leftRun.calls + rightRun.calls + 1,
                headRun.misses + tailRun.misses + leftRun.misses + rightRun.misses + 1,
                (memoFind (left, right) state.cache).2 + headRun.comparisons +
                  tailRun.comparisons + leftRun.comparisons + rightRun.comparisons⟩ := by
            rw [memoLcs]
            simp only [hread, hl, hr, dite_false]
            dsimp only [result, headRun, tailRun, leftRun, rightRun, queried, recordLookup] at *
            rw [← hhc, ← htc, ← hdlc, ← hdrc]
          refine ⟨recordComplete listOps (left, right) result dropRight, ?_, ?_⟩
          · rw [eval, read_eq_memoFind]
            simp only [hread]
            simp only [body, hl, hr, ite_false]
            simp only [Body.run, bind, EStateM.bind, pure, EStateM.pure]
            rw [hh]
            dsimp only
            rw [ht]
            dsimp only
            rw [hdl]
            dsimp only
            rw [hdr]
            dsimp only
            rw [hold]
          · rw [hold]
            simp only [recordComplete, listOps, ListCache.ops, Event.calls, Event.completedKeys,
              Event.lookupWork, List.length_cons]
            dsimp only [headRun, tailRun, leftRun, rightRun] at *
            simp only [queried, recordLookup, Event.calls, Event.completedKeys, Event.lookupWork] at *
            exact ⟨trivial, by omega, by omega, by omega⟩

theorem sound_of_memoSound (table : MemoTable) (hs : MemoSound table) :
    listOps.Sound score table := by
  intro key value hv
  rw [contents_eq_memoLookup] at hv
  exact memoLookup_sound hs key.1 key.2 hv

def envelope (left right : DyckWord) : Finset MemoKey :=
  (BalancedDecomposition.states left) ×ˢ (BalancedDecomposition.states right)

theorem envelope_closed (left right : DyckWord) (key : MemoKey)
    (hk : key ∈ envelope left right) (child : MemoKey)
    (hc : child ∈ (Body.meaning score (body key)).requests) : child ∈ envelope left right := by
  obtain ⟨hl, hr⟩ := Finset.mem_product.mp hk
  rw [body_requests] at hc
  by_cases hz : key.1 = 0 ∨ key.2 = 0
  · simp [hz] at hc
  · have hleft := BalancedDecomposition.states_closed hl (fun he => hz (Or.inl he))
    have hright := BalancedDecomposition.states_closed hr (fun he => hz (Or.inr he))
    simp [hz] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact Finset.mem_product.mpr ⟨hleft.1, hright.1⟩
    · exact Finset.mem_product.mpr ⟨hleft.2.1, hright.2.1⟩
    · exact Finset.mem_product.mpr ⟨hleft.2.2, hr⟩
    · exact Finset.mem_product.mpr ⟨hl, hright.2.2⟩

/-- A genuine local consumer of the generic nonuniform-envelope theorem. Warm
entries outside the D-product are allowed and need not be counted as new work. -/
theorem roots_envelope_spec (left right : DyckWord) (table : MemoTable) (roots : List MemoKey)
    (hv : (table.map Prod.fst).Nodup) (hs : MemoSound table)
    (hroots : ∀ key ∈ roots, key ∈ envelope left right) :
    ∃ final, evalRoots listOps body (left.semilength + right.semilength + 1) roots
        ⟨table, []⟩ = .ok (roots.map score) final ∧
      TraceInvariant listOps problem table final ∧
      (Event.completedKeys final.events).length ≤
        ((envelope left right).filter fun key => (memoLookup key table).isNone).card ∧
      Event.calls final.events ≤ roots.length +
        4 * ((envelope left right).filter fun key => (memoLookup key table).isNone).card := by
  have hbound : ∀ key ∈ roots, problem.rank key < left.semilength + right.semilength + 1 := by
    intro key hk
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp (hroots key hk)
    have hleft := BalancedDecomposition.states_semilength_le hl
    have hright := BalancedDecomposition.states_semilength_le hr
    dsimp [problem]
    omega
  simpa [problem, contents_eq_memoLookup, Nat.mul_comm]
    using roots_envelope listOps problem (envelope left right) (fun _ => 4)
      (envelope_closed left right) (fun key _ => body_request_bound score key.1 key.2)
      (left.semilength + right.semilength + 1) roots table hv (sound_of_memoSound table hs)
      hbound hroots

/-- Recover the established single-root constant by the generic exact-request
theorem, after identifying actual values, tables and counters. The original
unconditional counter theorem is retained unchanged. -/
theorem memoLcs_calls_from_generic (left right : DyckWord) (table : MemoTable)
    (hv : (table.map Prod.fst).Nodup) (hs : MemoSound table) :
    (memoLcs left right table).calls ≤ 4 * (memoLcs left right table).misses + 1 := by
  let fuel := left.semilength + right.semilength + 1
  obtain ⟨final, hr, _, hcalls, hmisses, _⟩ :=
    eval_refines_memoLcs fuel left right ⟨table, []⟩ (by dsimp [fuel]; omega)
  obtain ⟨same, he, _, ht⟩ := eval_trace_spec listOps problem table fuel (left, right)
    ⟨table, []⟩ hv (sound_of_memoSound table hs) (by dsimp [problem, fuel]; omega)
    (TraceInvariant.initial listOps problem table)
  have hsame : final = same := (EStateM.Result.ok.inj (hr.symm.trans he)).2
  rw [← hsame] at ht
  have hroots : evalRoots listOps problem.body fuel [(left, right)] ⟨table, []⟩ =
      .ok [(memoLcs left right table).value] final := by
    simp [evalRoots, bind, EStateM.bind, pure, EStateM.pure, problem, hr]
  have hcount := roots_call_bound listOps problem 4 fuel [(left, right)] table hroots ht
    (fun key _ => body_request_bound score key.1 key.2)
  simp only [Event.calls, Event.completedKeys, List.length_nil, Nat.zero_add] at hcalls hmisses
  simp only [List.length_cons, List.length_nil] at hcount
  omega

/-- Actual old-evaluator misses count only initially absent reachable keys,
even if the warm table contains unrelated independently correct entries. -/
theorem memoLcs_warm_misses_from_generic (left right : DyckWord) (table : MemoTable)
    (hv : (table.map Prod.fst).Nodup) (hs : MemoSound table) :
    (memoLcs left right table).misses ≤
      ((envelope left right).filter fun key => (memoLookup key table).isNone).card := by
  obtain ⟨final, hr, _, _, hmisses, _⟩ :=
    eval_refines_memoLcs (left.semilength + right.semilength + 1) left right
      ⟨table, []⟩ (by omega)
  have hroot : evalRoots listOps body (left.semilength + right.semilength + 1)
      [(left, right)] ⟨table, []⟩ = .ok [(memoLcs left right table).value] final := by
    simp [evalRoots, bind, EStateM.bind, pure, EStateM.pure, hr]
  obtain ⟨same, he, _, hm, _⟩ := roots_envelope_spec left right table [(left, right)] hv hs (by
    intro key hk
    simp only [List.mem_singleton] at hk
    subst key
    exact Finset.mem_product.mpr
      ⟨BalancedDecomposition.mem_states_self _, BalancedDecomposition.mem_states_self _⟩)
  have hsame : final = same := (EStateM.Result.ok.inj (hroot.symm.trans he)).2
  rw [← hsame] at hm
  simp only [Event.completedKeys, List.length_nil, Nat.zero_add] at hmisses
  rw [hmisses] at hm
  exact hm

end SubtreeProofs.Complexity.Paper2004
