module

public import SubtreeProofs.Rust.LookupSpatialPrimitives
public import SubtreeProofs.Rust.LookupTypeExecution
public import SubtreeProofs.Rust.LookupFrameExecution

/-! Spatially separated intermediate execution states and callee frames.
The guard certificate supplies no-owner clobbers and return cleanup; static
constraints supply destination bounds. Neither is substituted for separation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

def CallsSpatial (call : Calls) (good : Frame.CallSafety) : Prop :=
  ∀ function cells memory cell after cost, Frame.ArgsMatch function cells →
    call function cells memory = some (cell, after, cost) →
    good function cells memory cell after cost ∧
    ∀ frame, Separated memory (cells ++ frame) → Separated after (cell :: frame) ∧ Extends memory after

def ActionSpatial (call : Calls) (good : Frame.CallSafety) (count : Nat) (frame : List Cell)
    (memory : Memory) (env : Locals) : Action → Prop
  | .scope _ | .dropMoved _ => True
  | .assign _ rhs => ∀ cell middle, rvalue memory env rhs = some (cell, middle) →
      Separated memory (cell :: (values count middle ++ frame))
  | .call function args _ => ∀ cells middle, operands memory args env = some (cells, middle) →
      Separated memory (cells ++ (values count middle ++ frame)) ∧
      ∀ cell after cost, call function cells memory = some (cell, after, cost) →
        good function cells memory cell after cost

theorem action_spatial {call : Calls} {good : Frame.CallSafety} (hcall : CallsSpatial call good)
    {memory after : Memory} {locals : List Ty} {env env' : Locals} {cost : Cost} {frame : List Cell}
    (hb : Bounded locals.length env) (hs : Separated memory (values locals.length env ++ frame))
    (instruction : Action) (ht : SourceTypes.ActionConstraints locals instruction)
    (hg : Frame.ActionSafe call good memory env instruction)
    (hr : action call memory env instruction = some (env', after, cost)) :
    Bounded locals.length env' ∧ Separated after (values locals.length env' ++ frame) ∧
      Extends memory after ∧ ActionSpatial call good locals.length frame memory env instruction := by
  cases instruction with
  | scope slot =>
    cases hr
    exact ⟨hb.clear slot, clear_transfer ht hg frame hs, .refl memory, trivial⟩
  | dropMoved slot =>
    have hn : env slot = none := hg
    simp only [action, hn, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact ⟨hb, hs, .refl memory, trivial⟩
  | assign slot rhs =>
    obtain ⟨ty, _, hd⟩ := ht
    have hslot : slot < locals.length := List.getElem?_eq_some_iff.mp hd |>.choose
    have hw : ActionSpatial call good locals.length frame memory env (.assign slot rhs) := by
      intro cell middle hx
      exact (rvalue_spatial hb rhs hx).2 frame hs
    simp only [action] at hr
    cases hx : rvalue memory env rhs with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨cell, middle⟩
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      have hb' := (rvalue_spatial hb rhs hx).1
      exact ⟨hb'.store hslot _, store_transfer hslot (hg cell middle hx) cell frame (hw cell middle hx),
        .refl memory, hw⟩
  | call function args slot =>
    obtain ⟨_, ty, _, _, hd⟩ := ht
    have hslot : slot < locals.length := List.getElem?_eq_some_iff.mp hd |>.choose
    have hw : ActionSpatial call good locals.length frame memory env (.call function args slot) := by
      intro cells middle hx
      have hprofile := (hg cells middle hx).2.1
      refine ⟨?_, fun cell after cost hr => (hcall _ _ _ _ _ _ hprofile hr).1⟩
      simpa only [List.append_assoc] using (operands_spatial hb args hx).2 frame hs
    simp only [action] at hr
    cases hx : operands memory args env with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨cells, middle⟩
      cases hy : call function cells memory with
      | none => simp [hx, hy] at hr
      | some pair =>
        rcases pair with ⟨cell, mem, inner⟩
        simp only [hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        have hb' := (operands_spatial hb args hx).1
        obtain ⟨hd, hprofile, _⟩ := hg cells middle hx
        obtain ⟨hp, hext⟩ := (hcall _ _ _ _ _ _ hprofile hy).2 (values locals.length middle ++ frame) (hw cells middle hx).1
        exact ⟨hb'.store hslot _, store_transfer hslot hd cell frame hp, hext, hw⟩

inductive Trace (call : Calls) (good : Frame.CallSafety) (count : Nat) (frame : List Cell) :
    Code → Memory → Locals → Result → Memory → Cost → Prop where
  | done {memory : Memory} {env : Locals} :
      Bounded count env → Separated memory (values count env ++ frame) →
      Trace call good count frame .done memory env (.next env) memory {}
  | ret {memory : Memory} {env : Locals} {cell : Cell} :
      Bounded count env → Separated memory (values count env ++ frame) → env 0 = some cell →
      Separated memory (cell :: frame) →
      Trace call good count frame .ret memory env (.returned cell) memory ⟨1, {}⟩
  | step {instruction : Action} {rest : Code} {memory middle after : Memory}
      {env next : Locals} {result : Result} {first last : Cost} :
      Bounded count env → Separated memory (values count env ++ frame) →
      action call memory env instruction = some (next, middle, first) →
      ActionSpatial call good count frame memory env instruction →
      Trace call good count frame rest middle next result after last →
      Trace call good count frame (.step instruction rest) memory env result after (first.plus last)
  | branchReturned {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : Code}
      {memory after : Memory} {env next : Locals} {actual : Key} {cell : Cell} {first : Cost} :
      Bounded count env → Separated memory (values count env ++ frame) →
      scrutinee memory env scrut = some (actual, next) →
      Bounded count next → Separated memory (values count next ++ frame) →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      Trace call good count frame arm memory next (.returned cell) after first →
      Trace call good count frame (.branch scrut key other yes no rest) memory env (.returned cell) after
        ((⟨1 + scrut.weight, {}⟩ : Cost).plus first)
  | branchNext {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : Code}
      {memory middle after : Memory} {env next resume : Locals} {actual : Key}
      {result : Result} {first last : Cost} :
      Bounded count env → Separated memory (values count env ++ frame) →
      scrutinee memory env scrut = some (actual, next) →
      Bounded count next → Separated memory (values count next ++ frame) →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      Trace call good count frame arm memory next (.next resume) middle first →
      Trace call good count frame rest middle resume result after last →
      Trace call good count frame (.branch scrut key other yes no rest) memory env result after
        (((⟨1 + scrut.weight, {}⟩ : Cost).plus first).plus last)

theorem Trace.erases {call : Calls} {good : Frame.CallSafety} {count : Nat} {frame : List Cell}
    {code : Code} {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (h : Trace call good count frame code memory env result after cost) :
    Heap.exec call code memory env = some (result, after, cost) := by
  induction h with
  | done => rfl
  | ret _ _ hr _ => simp [Heap.exec, hr]
  | step _ _ ha _ _ ih => simp [Heap.exec, ha, ih]
  | branchReturned _ _ hs _ _ hsel _ ih => simp [Heap.exec, hs, Frame.selected_exec hsel, ih]
  | branchNext _ _ hs _ _ hsel _ _ ih₁ ih₂ => simp [Heap.exec, hs, Frame.selected_exec hsel, ih₁, ih₂]

def Post (count : Nat) (frame : List Cell) (memory : Memory) : Result → Prop
  | .next env => Bounded count env ∧ Separated memory (values count env ++ frame)
  | .returned cell => Separated memory (cell :: frame)

theorem selected_constraints {locals : List Ty} {output : Ty} {actual key : Key} {other : Option Key}
    {yes no arm : Code} (hy : SourceTypes.CodeConstraints locals output yes)
    (hn : SourceTypes.CodeConstraints locals output no)
    (hs : selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm) :
    SourceTypes.CodeConstraints locals output arm := by
  by_cases ha : actual = key
  · simp only [selectBranch, ha, ite_true, Option.some.injEq] at hs
    subst arm; exact hy
  · by_cases hb : other.all (· = actual) = true
    · simp only [selectBranch, ha, ite_false, hb, ite_true, Option.some.injEq] at hs
      subst arm; exact hn
    · simp [selectBranch, ha, hb] at hs

theorem exec_spatial {call : Calls} {good : Frame.CallSafety} (hcall : CallsSpatial call good)
    {code : Code} {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (hg : Frame.Guarded call good code memory env result after cost)
    {locals : List Ty} {output : Ty} {frame : List Cell}
    (ht : SourceTypes.CodeConstraints locals output code) (hb : Bounded locals.length env)
    (hs : Separated memory (values locals.length env ++ frame)) :
    Trace call good locals.length frame code memory env result after cost ∧
      Post locals.length frame after result ∧ Extends memory after := by
  induction hg generalizing locals output with
  | done => exact ⟨.done hb hs, ⟨hb, hs⟩, .refl _⟩
  | ret hr hd =>
    cases ht with
    | ret hret =>
      have hslot : 0 < locals.length := List.getElem?_eq_some_iff.mp hret |>.choose
      have hout := return_transfer hslot hr hd frame hs
      exact ⟨.ret hb hs hr hout, hout, .refl _⟩
  | step ha hg hrest ih =>
    cases ht with
    | step hi ht =>
      obtain ⟨hb', hs', hex, hw⟩ := action_spatial hcall hb hs _ hi hg ha
      obtain ⟨trace, post, hex'⟩ := ih ht hb' hs'
      exact ⟨.step hb hs ha hw trace, post, hex.trans hex'⟩
  | branchReturned hscrut hsel harm ih =>
    cases ht with
    | branch hst hk ho hy hn hrest =>
      obtain ⟨hb', htransfer⟩ := scrutinee_spatial hb _ hscrut
      have hs' := htransfer frame hs
      obtain ⟨trace, post, hex⟩ := ih (selected_constraints hy hn hsel) hb' hs'
      exact ⟨.branchReturned hb hs hscrut hb' hs' hsel trace, post, hex⟩
  | branchNext hscrut hsel harm hrest ihArm ihRest =>
    cases ht with
    | branch hst hk ho hy hn ht =>
      obtain ⟨hb', htransfer⟩ := scrutinee_spatial hb _ hscrut
      have hs' := htransfer frame hs
      obtain ⟨trace₁, post₁, hex₁⟩ := ihArm (selected_constraints hy hn hsel) hb' hs'
      obtain ⟨trace₂, post₂, hex₂⟩ := ihRest ht post₁.1 post₁.2
      exact ⟨.branchNext hb hs hscrut hb' hs' hsel trace₁ trace₂, post₂, hex₁.trans hex₂⟩

end SubtreeProofs.Rust.LookupSource.Heap.Spatial
