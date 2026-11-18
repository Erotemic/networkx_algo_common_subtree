module

public import SubtreeProofs.Rust.SourcePrefixIdentity

/-! A finite certificate bounds parent-root changes in actual prefixes. Calls
preserve the parent root map; only storage opening and retirement contribute. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def rootChangesBelow (limit : Nat) : Action → Bool
  | .storageLive slot | .storageDead slot => decide (slot < limit)
  | _ => true

theorem Calling.Prefix.root_above {callee : Derived.Callees} {callers : List Activation} {suffix : Code} {actions : List Action}
    {world final : World} {active after : Activation} (run : Calling.Prefix callee callers suffix actions world active final after)
    {limit slot : Nat} (above : limit ≤ slot) (bounded : actions.all (rootChangesBelow limit) = true) :
    after.roots slot = active.roots slot := by
  apply run.shape.2.2
  intro act member
  have bound := List.all_eq_true.mp bounded act member
  cases act with
  | storageLive destination | storageDead destination =>
    have small : destination < limit := of_decide_eq_true bound
    change slot ≠ destination
    omega
  | assign _ _ | drop _ | fakeRead _ | call _ _ _ | undefinedBehavior => trivial

end SubtreeProofs.Rust.SourceEval.Addressed
