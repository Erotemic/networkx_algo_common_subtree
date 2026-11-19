module

public import SubtreeProofs.Rust.SourceEvalHelperCalls
public import SubtreeProofs.Rust.SourceHeapDriverReflection

/-! Complete helper source/cost correspondence from successful concrete
execution and the existing scalar-width domain. Native depth/success witnesses
are not premises. The concrete helper implementations and their costs are
unchanged; ordinary reflection and existing mixed-world contracts compose. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource LookupSource.Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem lookup_reflect (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : LookupSource.Function) (packets : List ValueCell)
    (hb : Legacy.FieldsBounded (packets.map Prod.snd))
    (hp : RepresentsFields world.memory (packets.map Prod.fst) (packets.map Prod.snd))
    {packet : ValueCell} {cost : SourceEval.Cost}
    (h : lookup fuel budget world function packets = some (final, packet, cost)) :
    SourceEval.run SourceEval.Certificate.original.body fuel (SourceEval.Helpers.lookupFunction function) (packets.map Prod.snd) =
        some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      ∀ guards, Keeps world final guards := by
  cases hr : Heap.run LookupSource.Program.body fuel function (packets.map Prod.fst) world.memory with
  | none => simp [lookup, finish, hr] at h
  | some result =>
    rcases result with ⟨cell, memory, work⟩
    obtain ⟨value, hs, _, _⟩ := Heap.run_reflect LookupSource.Program.body fuel function world.memory _ _ _ _ _ hp hr
    rw [← LookupSource.Certificate.original_run] at hs
    exact lookup_spec fuel budget hw function packets hb hp hs h

theorem memo_reflect (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : MemoSource.Function) (packets : List ValueCell)
    (hb : Legacy.FieldsBounded (packets.map Prod.snd))
    (hp : RepresentsFields world.memory (packets.map Prod.fst) (packets.map Prod.snd))
    {packet : ValueCell} {cost : SourceEval.Cost}
    (h : memo fuel budget world function packets = some (final, packet, cost)) :
    SourceEval.run SourceEval.Certificate.original.body fuel (SourceEval.Helpers.memoFunction function) (packets.map Prod.snd) =
        some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      ∀ guards, Keeps world final guards := by
  cases hr : MemoSource.Heap.run MemoSource.Program.body fuel function (packets.map Prod.fst) world.memory with
  | none => simp [memo, finish, hr] at h
  | some result =>
    rcases result with ⟨cell, memory, work⟩
    obtain ⟨value, hs, _, _⟩ := MemoSource.Heap.run_reflect MemoSource.Program.body fuel function world.memory _ _ _ _ _ hp hr
    rw [← MemoSource.Certificate.original_run] at hs
    exact memo_spec fuel budget hw function packets hb hp hs h

theorem readable_number_source {memory : Memory} {live : Live} {number : Nat} {value : Value}
    (h : Readable memory live (.number number) value) : value = .number number := by
  obtain ⟨_, hg, _⟩ := h
  cases hg
  rfl

theorem boxNew_ready {fuel : Nat} {world final : World} {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (h : boxNew fuel world packets = some (final, packet, cost)) : Ready fuel .boxNew packets := by
  unfold boxNew at h
  split at h
  next fuel cell value => exact .boxNew cell value (by omega)
  next => cases h

theorem checkedAdd_ready {fuel : Nat} {world final : World} {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (h : checkedAdd fuel world packets = some (final, packet, cost)) : Ready fuel .checkedAdd packets := by
  unfold checkedAdd at h
  split at h
  next fuel left leftValue right rightValue =>
    split at h
    next bounds =>
      have hl := readable_number_source (hp (.number left, leftValue) (by simp))
      have hr := readable_number_source (hp (.number right, rightValue) (by simp))
      dsimp only at hl hr
      subst leftValue rightValue
      exact .checkedAdd left right (by omega) bounds.1 bounds.2
    next => cases h
  next => cases h

theorem callee_bounded_respects (fuel budget : Nat) :
    Derived.CallsRespect (callee fuel budget) (SourceEval.run SourceEval.Certificate.original.body fuel)
      (fun _ _ packets => Legacy.FieldsBounded (packets.map Prod.snd)) := by
  intro world guards suspended function packets final packet cost hw hp hc hl hb hrun
  have represented := packets_represented hp
  cases function with
  | copyWord | compare | copyResult | lookup =>
    all_goals
      obtain ⟨hs, hr, hf, hk⟩ := lookup_reflect fuel budget hw _ packets hb represented hrun
      exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | concatenate | insert =>
    all_goals
      obtain ⟨hs, hr, hf, hk⟩ := memo_reflect fuel budget hw _ packets hb represented hrun
      exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | boxNew =>
    exact callee_respects fuel budget world guards suspended .boxNew packets final packet cost hw hp hc hl (boxNew_ready hrun) hrun
  | checkedAdd =>
    exact callee_respects fuel budget world guards suspended .checkedAdd packets final packet cost hw hp hc hl (checkedAdd_ready hp hrun) hrun
  | chooseLonger | evaluate | maximum => cases hrun

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
