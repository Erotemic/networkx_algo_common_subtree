module

public import SubtreeProofs.Rust.SourceLoanSafeMachine

/-! Prefix proofs retain the actual continuation when preparing reference views.
The existing calling executor still determines every primitive, guard and cost;
these traces compose its constructed steps with a later suffix execution. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LoanEnding

open LookupSource Partial

theorem forget_eq_or_empty (code : Code) (slots : List Nat) (state : State) (index : Nat) :
    forget code slots state index = state index ∨ forget code slots state index = .empty := by
  induction slots generalizing state with
  | nil => exact Or.inl rfl
  | cons slot rest ih =>
    rw [forget_cons]
    cases hs : state slot <;> try exact ih state
    by_cases ended : endsBeforeObservation slot code = true
    · simp only [ended, ite_true]
      rcases ih (state.set slot .empty) with same | empty
      · by_cases eq : index = slot
        · exact Or.inr (same.trans (by simp only [Locals.set, eq, ite_true]))
        · exact Or.inl (same.trans (by simp only [Locals.set, eq, ite_false]))
      · exact Or.inr empty
    · simpa only [ended, Bool.false_eq_true, ite_false] using ih state

theorem forget_empty (code : Code) (slots : List Nat) {state : State} {index : Nat} (empty : state index = .empty) :
    forget code slots state index = .empty := by
  rcases forget_eq_or_empty code slots state index with same | cleared
  · exact same.trans empty
  · exact cleared

end SubtreeProofs.Rust.SourceEval.LoanEnding

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Partial Partial.Addressed Storage

inductive Prefix (callee : Derived.Callees) (callers : List Activation) (suffix : Code) :
    List Action → World → Activation → World → Activation → Prop where
  | nil (world : World) (active : Activation) : Prefix callee callers suffix [] world active world active
  | cons {world middle final : World} {active current after : Activation} {act : Action} {rest : List Action} {cost : Cost} :
      instruction callee callers (world, active.forgetRefs ((act :: rest).foldr Control.Tree.step suffix)) act =
        some ((middle, current), cost) →
      Prefix callee callers suffix rest middle current final after →
      Prefix callee callers suffix (act :: rest) world active final after

theorem Prefix.exec {callee : Derived.Callees} {callers : List Activation} {suffix : Code} {actions : List Action}
    {world final : World} {active after : Activation} (h : Prefix callee callers suffix actions world active final after)
    {flow : Derived.Flow} {last : Cost} (tail : exec callee callers suffix final after = some (flow, last)) :
    ∃ cost, exec callee callers (actions.foldr Control.Tree.step suffix) world active = some (flow, cost) := by
  induction h with
  | nil => exact ⟨last, tail⟩
  | @cons world middle final active current after act rest firstCost first _ ih =>
    obtain ⟨cost, run⟩ := ih tail
    simp only [List.foldr_cons] at first
    refine ⟨firstCost.plus cost, ?_⟩
    rw [List.foldr_cons, exec_step]
    dsimp only
    rw [first]
    simp only [run, bind, Option.bind]

theorem Prefix.append {callee : Derived.Callees} {callers : List Activation} {suffix : Code} {first rest : List Action}
    {world middle final : World} {active current after : Activation}
    (head : Prefix callee callers (rest.foldr Control.Tree.step suffix) first world active middle current)
    (tail : Prefix callee callers suffix rest middle current final after) :
    Prefix callee callers suffix (first ++ rest) world active final after := by
  induction head with
  | nil => exact tail
  | @cons world middle final active current after act remaining firstCost step _ ih =>
    apply Prefix.cons (cost := firstCost) ?_ (ih tail)
    change instruction callee callers (world, active.forgetRefs (((act :: remaining) ++ rest).foldr Control.Tree.step suffix)) act = _
    rw [List.foldr_append]
    exact step

theorem Prefix.noncall_callee {first : Derived.Callees} (second : Derived.Callees)
    {callers : List Activation} {suffix : Code} {actions : List Action}
    {world final : World} {active after : Activation}
    (h : Prefix first callers suffix actions world active final after)
    (closed : noCalls (actions.foldr Control.Tree.step .done) = true) :
    Prefix second callers suffix actions world active final after := by
  induction h with
  | nil => exact .nil _ _
  | @cons world middle final active current after act rest cost run _ ih =>
    cases act with
    | call _ _ _ => cases closed
    | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior =>
      all_goals exact .cons run (ih closed)

theorem instruction_call_run {callee : Derived.Callees} {callers : List Activation} {world final : World}
    {active after : Activation} {function : Function} {args : List Operand} {slot : Nat} {cost : Cost}
    (run : Derived.call callee world active callers function args slot = some (final, after, cost)) :
    instruction callee callers (world, active) (.call function args slot) = some ((final, after), cost) := by
  change (do let (world, active, cost) ← Derived.call callee world active callers function args slot
             some ((world, active), cost)) = _
  rw [run]
  rfl

theorem instruction_noncall_run {callee : Derived.Callees} {callers : List Activation} {world final : World}
    {active after : Activation} {act : Action} (run : Derived.action world active callers act = some (final, after)) :
    instruction callee callers (world, active) act = some ((final, after), Derived.actionCost active act) := by
  cases act with
  | call _ _ _ | undefinedBehavior => cases run
  | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ =>
    all_goals change (do let (world, active) ← Derived.action world active callers _; some ((world, active), _)) = _
    all_goals rw [run]; rfl

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
