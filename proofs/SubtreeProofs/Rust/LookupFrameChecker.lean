module

public import SubtreeProofs.Rust.LookupFrameState

/-! Executable conservative frame analysis. This checks move availability,
callee ownership profiles, clobbers, and return cleanup. Copy/borrow reads
remain subject to the concrete interpreter's read validity rules. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Frame

def inferOperand (state : State) : Operand → Option (Bool × State)
  | .move slot => do
    if slot < state.length then
      let flag ← lookup state slot
      some (flag, state.set slot none)
    else none
  | .copy _ | .boolean _ => some (false, state)

def inferOperands : State → List Operand → Option (List Bool × State)
  | state, [] => some ([], state)
  | state, first :: rest => do
    let (flag, state) ← inferOperand state first
    let (flags, state) ← inferOperands state rest
    some (flag :: flags, state)

def inferRValue (state : State) : RValue → Option (Bool × State)
  | .use op => inferOperand state op
  | .address _ => some (false, state)
  | .aggregate kind _ args => do
    let (flags, state) ← inferOperands state args
    some ((if kind = .tuple then flags.any id else true), state)

def inferScrutinee (state : State) : Scrutinee → Option State
  | .discriminant _ => some state
  | .value op => do
    let (flag, state) ← inferOperand state op
    if flag then none else some state

def store (state : State) (slot : Nat) (flag : Option Bool) : Option State :=
  if slot < state.length then
    if canClear state slot then some (state.set slot flag) else none
  else none

def callProfile (function : Function) (flags : List Bool) : Bool :=
  flags.length == arity function && (function == .boxNew || !(flags.any id))

def inferAction (state : State) : Action → Option State
  | .scope slot => store state slot none
  | .assign slot rhs => do
    let (flag, state) ← inferRValue state rhs
    store state slot (some flag)
  | .call function args slot => do
    let (flags, state) ← inferOperands state args
    if callProfile function flags then store state slot (some (outputFlag function)) else none
  | .dropMoved slot =>
    if slot < state.length && lookup state slot == none then some state else none

def returnCheck (state : State) (output : Bool) : Bool :=
  lookup state 0 == some output &&
    (List.range state.length).all fun index => index == 0 || canClear state index

/-- Continuations check all fallthrough states; early returns check cleanup
and skip that continuation. This avoids an unsound join of owned slot states. -/
def verify : Code → State → Bool → (State → Bool) → Bool
  | .done, state, _, post => post state
  | .ret, state, output, _ => returnCheck state output
  | .step instruction rest, state, output, post =>
    match inferAction state instruction with
    | none => false
    | some next => verify rest next output post
  | .branch scrut _ _ yes no rest, state, output, post =>
    match inferScrutinee state scrut with
    | none => false
    | some next =>
      verify yes next output (fun s => verify rest s output post) &&
      verify no next output (fun s => verify rest s output post)

theorem store_spec {state next : State} {env : Locals} {slot : Nat}
    {flag : Option Bool} {cell : Option Cell} (he : StateRep state env)
    (hm : Option.Rel Matches flag cell) (hs : store state slot flag = some next) :
    StateRep next (env.set slot cell) ∧ Disposable (env slot) := by
  unfold store at hs
  split at hs
  next hb =>
    split at hs
    next hc =>
      cases hs
      exact ⟨he.set slot hb hm, he.clear hc⟩
    next => cases hs
  next => cases hs

theorem store_disposable {state next : State} {env : Locals} {slot : Nat} {flag : Option Bool}
    (he : StateRep state env) (hs : store state slot flag = some next) : Disposable (env slot) := by
  unfold store at hs
  split at hs
  next =>
    split at hs
    next hc => exact he.clear hc
    next => cases hs
  next => cases hs

theorem return_spec {state : State} {env : Locals} {output : Bool} (he : StateRep state env)
    (hc : returnCheck state output = true) {cell : Cell} (hr : env 0 = some cell) :
    Matches output cell ∧ ∀ index, index ≠ 0 → Disposable (env index) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hzero : lookup state 0 = some output := by simpa using hh.1
  refine ⟨he.get hzero hr, ?_⟩
  intro index hi
  by_cases hb : index < state.length
  · have hs := List.all_eq_true.mp hh.2 index (List.mem_range.mpr hb)
    have hclear : canClear state index = true := by simpa [hi] using hs
    exact he.clear hclear
  · have hn : lookup state index = none := by
      simp [lookup, List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hb)]
    rw [he.empty hn]
    trivial

end SubtreeProofs.Rust.LookupSource.Heap.Frame
