module

public import SubtreeProofs.Rust.SourceEvalCallingEntry
public import SubtreeProofs.Rust.SourceEvalTypeBounds

/-! Derive every selected call's input domain from the independently checked
source types and actual operand execution. The local callee source contract is
consumed only at that call. No native depth bound or desired parent outcome is
assumed; successful physical execution remains separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap

def TypedReady : Ready := fun _ function packets =>
  ∃ types ty, SnapshotFieldsTyped (packets.map Prod.snd) types ∧ Types.callOutput function types = some ty

end SubtreeProofs.Rust.SourceEval.Addressed.Derived

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap LookupSource.Partial LookupSource.Partial.Addressed Storage Derived

theorem readyAt_typed {world : World} {active : Activation} {callers : List Activation} {locals : List Ty}
    (ha : active.Valid world) (he : LocalsTyped locals active.state) (act : Action)
    (ht : Types.ActionConstraints locals act) : ReadyAt Derived.TypedReady world active callers act := by
  cases act with
  | call function args slot =>
    intro current suspended packets masks _ _ hargs
    obtain ⟨types, ty, hops, hout, _⟩ := ht
    obtain ⟨_, guards, hf⟩ := ha
    obtain ⟨_, hs, _, _, _⟩ := Addressed.operands_spec hf args hargs
    exact ⟨types, ty, (Types.operands_typed he args hops hs).1, hout⟩
  | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior => trivial

theorem readyFor_typed {callee : Derived.Callees} {source : Calls}
    (hcallee : Derived.CallsRespect callee source Derived.TypedReady) (hsource : Types.CallsTyped source)
    {locals : List Ty} {output : Ty} {code : Code} (ht : Types.CodeConstraints locals output code)
    {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (he : LocalsTyped locals active.state) : ReadyFor callee Derived.TypedReady callers code world active := by
  induction ht generalizing world active with
  | done | ret => trivial
  | @step act rest hact hrest ih =>
    have observed := Activation.forgetRefs_valid ha (.step act rest)
    have typed := Activation.forgetRefs_typed he (.step act rest)
    have ready := readyAt_typed (callers := callers) observed typed act hact
    refine ⟨ready, ?_⟩
    intro middle current first hr
    have step := instruction_spec hcallee observed hc hw act ready hr
    exact ih step.valid step.callers step.wellFormed (Types.action_typed hsource typed act hact step.source)
  | @switch scrut branches fallback left right rest kind hs _ hleft hright hrest ihLeft ihRight ihRest =>
    intro key current hscrut
    obtain ⟨hread, _, _, _, hcurrent⟩ := Derived.scrutinee_spec ha scrut hscrut
    have typed := Types.scrutinee_typed he scrut hs hread
    have leftReady := ihLeft hcurrent hc hw typed
    have rightReady := ihRight hcurrent hc hw typed
    refine ⟨fun _ _ => ⟨fun _ => leftReady, fun _ => rightReady⟩, ?_⟩
    intro middle resume first hb
    have selected : (Flow.next middle resume).Valid callers ∧
        Types.OutcomeTyped locals output (Flow.next middle resume).snapshot := by
      apply selected_spec key branches fallback
        (PL := True) (PR := True)
        (P := fun (r : Flow × Cost) => r.1.Valid callers ∧ Types.OutcomeTyped locals output r.1.snapshot)
        (fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩) ?_ ?_ hb
      · intro _ result hr
        have h := exec_spec hcallee hcurrent hc hw left leftReady hr
        exact ⟨h.2.2.2, Types.exec_typed hsource typed hleft h.1⟩
      · intro _ result hr
        have h := exec_spec hcallee hcurrent hc hw right rightReady hr
        exact ⟨h.2.2.2, Types.exec_typed hsource typed hright h.1⟩
    exact ihRest selected.1.active selected.1.callers selected.1.wellFormed selected.2

theorem exec_typed_spec {callee : Derived.Callees} {source : Calls}
    (hcallee : Derived.CallsRespect callee source Derived.TypedReady) (hsource : Types.CallsTyped source)
    {locals : List Ty} {output : Ty} {code : Code} (ht : Types.CodeConstraints locals output code)
    {world : World} {active : Activation} {callers : List Activation} {result : Flow} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (he : LocalsTyped locals active.state) (hr : exec callee callers code world active = some (result, cost)) :
    SourceEval.exec source code active.state = some (result.snapshot, cost) ∧
      result.activation.frame = active.frame ∧ result.activation.count = active.count ∧ result.Valid callers ∧
      Types.OutcomeTyped locals output result.snapshot := by
  have h := exec_spec hcallee ha hc hw code (readyFor_typed hcallee hsource ht ha hc hw he) hr
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, Types.exec_typed hsource he ht h.1⟩

theorem fields_typed_length {values : List Value} {types : List Ty} (h : SnapshotFieldsTyped values types) :
    values.length = types.length := by
  induction values generalizing types with
  | nil => cases h; rfl
  | cons first rest ih =>
    cases h with
    | cons _ tail => simp only [List.length_cons, ih tail]

theorem invoke_typed_ready {callee : Derived.Callees} {source : Calls}
    (hcallee : Derived.CallsRespect callee source Derived.TypedReady) (hsource : Types.CallsTyped source)
    (decl : TypeReader.Definition) {world : World} {callers : List Activation} {packets : List ValueCell}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : SnapshotFieldsTyped (packets.map Prod.snd) (Types.inputs decl.source.function)) :
    ReadyFor callee Derived.TypedReady callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets) := by
  have arity : packets.length = (Types.inputs decl.source.function).length := by
    simpa only [List.length_map] using fields_typed_length ht
  obtain ⟨_, ha, hentered, hkept⟩ := enter_definition hw world.memory.length decl hp arity
  have hcallers : ∀ a ∈ callers, a.Valid (world.stackCells world.memory.length (packets.map Prod.fst)) := by
    intro a hm
    obtain ⟨bound, used, hf⟩ := hc a hm
    exact ⟨bound, used, hf.preserve (hkept used).preserves⟩
  exact readyFor_typed hcallee hsource decl.constraints ha hcallers hentered (Types.initial_typed ht decl.boundary)

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
