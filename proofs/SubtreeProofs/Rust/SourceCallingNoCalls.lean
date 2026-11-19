module

public import SubtreeProofs.Rust.SourceEvalGuardedEntry

/-! Call-free actual code is independent of the supplied callee dispatcher.
Reference preparation, physical guards, routing, costs, entry and closure all
remain in the existing executor. This transfers constructed leaf executions
to recursive dispatchers, including dispatchers with no remaining call fuel. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Partial Partial.Addressed Storage

theorem exec_noCalls (first second : Derived.Callees) (callers : List Activation)
    (code : Code) (closed : noCalls code = true) (world : World) (active : Activation) :
    exec first callers code world active = exec second callers code world active := by
  induction code generalizing world active with
  | done | ret => rfl
  | step act rest ih =>
    cases act with
    | call _ _ _ => cases closed
    | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior =>
      all_goals
        rw [exec_step, exec_step]
        simp_rw [ih closed]
        rfl
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    have parts := Bool.and_eq_true_iff.mp closed
    have branches := Bool.and_eq_true_iff.mp parts.1
    rw [exec_switch, exec_switch]
    simp_rw [ihLeft branches.1, ihRight branches.2, ihRest parts.2]

theorem invoke_noCalls (first second : Derived.Callees) (callers : List Activation) (guards : List Nat)
    (decl : TypeReader.Definition) (closed : noCalls decl.source.code = true)
    (world : World) (packets : List ValueCell) :
    invoke first callers guards decl world packets = invoke second callers guards decl world packets := by
  unfold invoke
  simp_rw [exec_noCalls first second callers decl.source.code closed]

theorem guardedInvoke_noCalls (first second : Derived.Callees) (callers : List Activation) (guards : List Nat)
    (decl : TypeReader.Definition) (closed : noCalls decl.source.code = true)
    (world : World) (packets : List ValueCell) :
    guardedInvoke first callers guards decl world packets = guardedInvoke second callers guards decl world packets := by
  unfold guardedInvoke
  rw [invoke_noCalls first second callers guards decl closed world packets]

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
