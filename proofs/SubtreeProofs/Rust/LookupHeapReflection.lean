module

public import SubtreeProofs.Rust.LookupHeapReflectionPrimitives
public import SubtreeProofs.Rust.LookupHeapExecution

/-! Reflection of successful concrete helper control into the existing source
interpreter. Callees supply local reflection, including retained old memory.
Fuel induction discharges that contract for the actual helper drivers. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

def CallsReflect {F : Type} (concrete : CallsFor F) (abstract : CalleesFor F) : Prop :=
  ∀ function memory cells values cell after cost,
    RepresentsFields memory cells values → concrete function cells memory = some (cell, after, cost) →
    ∃ value, abstract function values = some (value, cost) ∧ Represents after cell value ∧ Extends memory after

theorem action_reflect {F : Type} {call : CallsFor F} {source : CalleesFor F}
    (hc : CallsReflect call source) {memory after : Memory} {concrete next : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (instruction : Action F) {cost : Cost}
    (hr : action call memory concrete instruction = some (next, after, cost)) :
    ∃ state, evalAction source abstract instruction = some (state, cost) ∧
      EnvRep after next state ∧ Extends memory after := by
  cases instruction with
  | scope slot =>
    cases hr
    exact ⟨abstract.set slot none, rfl, he.set slot .none, .refl memory⟩
  | assign slot rhs =>
    cases hs : rvalue memory concrete rhs with
    | none => simp [action, hs] at hr
    | some pair =>
      rcases pair with ⟨cell, state⟩
      simp only [action, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨value, middle, ht, hv, hm⟩ := rvalue_reflect he rhs hs
      exact ⟨middle.set slot (some value), by simp only [evalAction, ht, Bind.bind, Option.bind],
        hm.set slot (.some hv), .refl memory⟩
  | dropMoved slot =>
    cases hs : concrete slot with
    | some cell => simp [action, hs] at hr
    | none =>
      simp only [action, hs, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      have hn : abstract slot = none := by
        have hx := he slot
        rw [hs] at hx
        cases ht : abstract slot with
        | none => rfl
        | some value => rw [ht] at hx; cases hx
      exact ⟨abstract, by simp only [evalAction, hn], he, .refl memory⟩
  | call function args slot =>
    cases hs : operands memory args concrete with
    | none => simp [action, hs] at hr
    | some pair =>
      rcases pair with ⟨cells, state⟩
      cases hi : call function cells memory with
      | none => simp [action, hs, hi] at hr
      | some result =>
        rcases result with ⟨cell, middle, work⟩
        simp only [action, hs, hi, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨values, sourceState, ht, hv, hm⟩ := operands_reflect he args hs
        obtain ⟨value, hsource, hrep, hext⟩ := hc function memory cells values cell middle work hv hi
        exact ⟨sourceState.set slot (some value), by simp only [evalAction, ht, hsource, Bind.bind, Option.bind],
          (hm.mono hext).set slot (.some hrep), hext⟩

theorem exec_reflect {F : Type} {call : CallsFor F} {source : CalleesFor F}
    (hc : CallsReflect call source) (code : Code F) {memory after : Memory}
    {concrete : Locals} {abstract : Env} (he : EnvRep memory concrete abstract)
    {result : Result} {cost : Cost} (hr : exec call code memory concrete = some (result, after, cost)) :
    ∃ outcome, LookupSource.exec source code abstract = some (outcome, cost) ∧
      OutcomeRep after result outcome ∧ Extends memory after := by
  induction code generalizing memory after concrete abstract result cost with
  | done =>
    cases hr
    exact ⟨.next abstract, rfl, he, .refl memory⟩
  | ret =>
    cases hs : concrete 0 with
    | none => simp [exec, hs] at hr
    | some cell =>
      simp only [exec, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨value, ht, hv⟩ := he.source hs
      exact ⟨.returned value, by simp only [LookupSource.exec, ht, Bind.bind, Option.bind], hv, .refl memory⟩
  | step instruction rest ih =>
    cases ha : action call memory concrete instruction with
    | none => simp [exec, ha] at hr
    | some packet =>
      rcases packet with ⟨state, middle, first⟩
      cases hs : exec call rest middle state with
      | none => simp [exec, ha, hs] at hr
      | some packet =>
        rcases packet with ⟨last, final, second⟩
        simp only [exec, ha, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨sourceState, ha', hm, hex₁⟩ := action_reflect hc he instruction ha
        obtain ⟨outcome, hs', ho, hex₂⟩ := ih hm hs
        exact ⟨outcome, by simp only [LookupSource.exec, ha', hs', Bind.bind, Option.bind], ho, hex₁.trans hex₂⟩
  | branch scrut key other yes no rest ihYes ihNo ihRest =>
    cases hs : scrutinee memory concrete scrut with
    | none => simp [exec, hs] at hr
    | some pair =>
      rcases pair with ⟨actual, state⟩
      cases hb : selectBranch actual key other
          (fun _ => exec call yes memory state) (fun _ => exec call no memory state) with
      | none => simp [exec, hs, hb] at hr
      | some packet =>
        rcases packet with ⟨selected, middle, first⟩
        obtain ⟨sourceState, hs', hm⟩ := scrutinee_reflect he scrut hs
        have branch : ∃ outcome,
            selectBranch actual key other (fun _ => LookupSource.exec source yes sourceState)
              (fun _ => LookupSource.exec source no sourceState) = some (outcome, first) ∧
            OutcomeRep middle selected outcome ∧ Extends memory middle := by
          by_cases hy : actual = key
          · simpa only [selectBranch, hy, ite_true] using
              ihYes hm (by simpa only [selectBranch, hy, ite_true] using hb)
          · by_cases hn : other.all (· = actual) = true
            · simpa only [selectBranch, hy, ite_false, hn, ite_true] using
                ihNo hm (by simpa only [selectBranch, hy, ite_false, hn, ite_true] using hb)
            · simp [selectBranch, hy, hn] at hb
        obtain ⟨outcome, hb', ho, hex₁⟩ := branch
        cases selected with
        | returned cell =>
          simp only [exec, hs, hb, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          cases outcome with
          | next _ => cases ho
          | returned value =>
            exact ⟨.returned value, by simp only [LookupSource.exec, hs', hb', Bind.bind, Option.bind], ho, hex₁⟩
        | next state =>
          cases outcome with
          | returned _ => cases ho
          | next sourceNext =>
            cases ht : exec call rest middle state with
            | none => simp [exec, hs, hb, ht] at hr
            | some packet =>
              rcases packet with ⟨last, final, second⟩
              simp only [exec, hs, hb, ht, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl, rfl⟩ := hr
              obtain ⟨outcome, ht', ho', hex₂⟩ := ihRest ho ht
              exact ⟨outcome, by simp only [LookupSource.exec, hs', hb', ht', Bind.bind, Option.bind], ho', hex₁.trans hex₂⟩

end SubtreeProofs.Rust.LookupSource.Heap
