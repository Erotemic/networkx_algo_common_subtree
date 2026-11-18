module

public import SubtreeProofs.Rust.SourceAssignmentTotality

/-! Forward actual switch inspection. Discriminants require only retained node
tags, including after partial field moves. Boolean values use the same derived
move permissions and actual operand executor. Routing and branch costs remain
in the existing shared control engine. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def ScrutineeAllowed (world : World) (roots : Roots) (blocked : List Nat) : Scrutinee → Prop
  | .discriminant _ => True
  | .value operand => Allowed world roots blocked (Legacy.operandMap operand)

theorem scrutinee_complete {world : World} {roots : Roots} {frame : Nat} {state after : State}
    {guards blocked : List Nat} (hf : Frame world frame roots state guards)
    (scrut : Scrutinee) {key : Key} (source : SourceEval.scrutinee state scrut = some (key, after))
    (allowed : ScrutineeAllowed world roots blocked scrut) :
    scrutinee world roots blocked state scrut = some (key, after) := by
  cases scrut with
  | discriminant place =>
    rcases split : splitPlace place with ⟨slot, path⟩
    cases get : (state slot).get path with
    | none => simp [SourceEval.scrutinee, split, get] at source
    | some part => cases part with
      | empty | boolean _ | number _ | shared _ | boxed _ => simp [SourceEval.scrutinee, split, get] at source
      | node kind tag parts =>
        have read : (state (splitPlace place).1).get (splitPlace place).2 = some (.node kind tag parts) := by
          simpa only [split] using get
        have raw := discriminant_complete hf place read
        simp only [SourceEval.scrutinee, split, get, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at source
        obtain ⟨rfl, rfl⟩ := source
        simp only [scrutinee, raw, bind, Option.bind]
  | value operand =>
    rw [Types.scrutinee_value] at source
    cases execution : SourceEval.operand state (Legacy.operandMap operand) with
    | none => simp [execution] at source
    | some pair =>
      rcases pair with ⟨value, middle⟩
      cases value with
      | number _ | node _ _ _ | reference _ | boxed _ => simp [execution] at source
      | boolean b =>
        simp only [execution, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at source
        obtain ⟨rfl, rfl⟩ := source
        obtain ⟨cell, raw⟩ := operand_complete hf execution allowed
        obtain ⟨_, _, graph, _, _⟩ := operand_spec hf raw
        cases graph
        simp only [scrutinee, raw, bind, Option.bind]

end SubtreeProofs.Rust.SourceEval.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem scrutinee_complete {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world)
    (scrut : Scrutinee) {key : Key} {masks : State}
    (source : SourceEval.scrutinee active.state scrut = some (key, masks))
    (allowed : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      Addressed.ScrutineeAllowed world active.roots (current.loans ++ suspended.reads) scrut) :
    scrutinee world active callers scrut = some (key, {active with state := masks}) := by
  obtain ⟨current, hs, scanned⟩ := active.scan_complete ha
  obtain ⟨suspended, ht, callerView⟩ := scanCallers_complete callers hc
  have raw := Addressed.scrutinee_complete scanned.frame scrut source (allowed current suspended scanned callerView)
  simp only [scrutinee, hs, ht, raw, bind, Option.bind]

theorem scrutinee_total {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world)
    (scrut : Scrutinee) {key : Key} {masks : State} {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (source : SourceEval.scrutinee active.state scrut = some (key, masks))
    (allowed : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      Addressed.ScrutineeAllowed world active.roots (current.loans ++ suspended.reads) scrut) :
    scrutinee world active callers scrut = some (key, {active with state := masks}) ∧
      ({active with state := masks} : Activation).Valid world ∧
      OwnerFrame world (({active with state := masks} : Activation).owners world ++ (callerOwners world callers ++ external)) ∧
      BoxCoverage world (({active with state := masks} : Activation).owners world ++ (callerOwners world callers ++ external)) := by
  have run := scrutinee_complete ha hc scrut source allowed
  have valid := (scrutinee_spec ha scrut run).2.2.2.2
  exact ⟨run, valid, scrutinee_owner_resources ha scrut hf covered run⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
