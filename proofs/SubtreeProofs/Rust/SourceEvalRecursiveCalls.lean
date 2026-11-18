module

public import SubtreeProofs.Rust.SourceEvalGuardedEntry
public import SubtreeProofs.Rust.SourceEvalCallingCertificate

/-! Recursive addressed execution uses the existing six helper backends and two
intrinsics, and actual parsed entry/control/cleanup for choice, evaluator and
maximum. Fuel bounds call nesting. Input readiness is independent of source
answers; universal native readiness and physical success remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def interpreted : Function → Bool
  | .chooseLonger | .evaluate | .maximum => true
  | _ => false

def run (program : List TypeReader.Definition) (budget : Nat) : Nat → Derived.Callees
  | 0 => fun _ _ _ _ _ => none
  | fuel + 1 => fun world guards callers function packets =>
    if interpreted function then do
      let decl ← program.find? (fun decl => decl.source.function == function)
      Calling.guardedInvoke (run program budget fuel) callers guards decl world packets
    else Helpers.callee (fuel + 1) budget world guards callers function packets

/-- The leaf conditions are the existing native helper shapes/depths. An
interpreted body composes those input conditions along its actual selected
paths for each suspended caller stack; no desired source result occurs here. -/
def Ready (program : List TypeReader.Definition) (budget : Nat) : Nat → Derived.Ready
  | 0 => fun _ _ _ => True
  | fuel + 1 => fun world function packets =>
    if interpreted function then
      ∀ decl, program.find? (fun decl => decl.source.function == function) = some decl →
        ∀ callers, Calling.ReadyFor (run program budget fuel) (Ready program budget fuel) callers decl.source.code
          (world.stackCells world.memory.length (packets.map Prod.fst))
          (initialActivation world world.memory.length decl.source.localCount packets)
    else Helpers.Ready (fuel + 1) function packets

def Aligned (program : List TypeReader.Definition) : Prop :=
  ∀ decl ∈ program, decl.source.code = Certificate.original.body decl.source.function

theorem interpreted_nonintrinsic {function : Function} (h : interpreted function = true) :
    function ≠ .boxNew ∧ function ≠ .checkedAdd := by
  cases function <;> simp_all [interpreted]

theorem run_zero (program : List TypeReader.Definition) (budget : Nat) (world : World) (guards : List Nat)
    (callers : List Activation) (function : Function) (packets : List ValueCell) :
    run program budget 0 world guards callers function packets = none := rfl

theorem run_respects (program : List TypeReader.Definition) (aligned : Aligned program) (budget fuel : Nat) :
    Derived.CallsRespect (run program budget fuel) (SourceEval.run Certificate.original.body fuel) (Ready program budget fuel) := by
  induction fuel with
  | zero =>
    intro world guards callers function packets final packet cost hw hp hc hl hd h
    cases h
  | succ fuel ih =>
    intro world guards callers function packets final packet cost hw hp hc hl hd h
    by_cases hi : interpreted function = true
    · simp only [run, hi, ite_true] at h
      cases hf : program.find? (fun decl => decl.source.function == function) with
      | none => simp [hf] at h
      | some decl =>
        simp only [hf, Bind.bind, Option.bind] at h
        have hpredicate : (decl.source.function == function) = true := List.find?_some (p := fun (entry : TypeReader.Definition) => entry.source.function == function) hf
        have hfunction : decl.source.function = function := beq_iff_eq.mp hpredicate
        have hcode := aligned decl (List.mem_of_find?_eq_some hf)
        have hordinary := interpreted_nonintrinsic (function := decl.source.function) (by simpa only [hfunction] using hi)
        simp only [Ready, hi, ite_true] at hd
        have hs := Calling.guardedInvoke_spec ih decl hcode hordinary.1 hordinary.2 hw hc hp (hd decl hf callers) h
        simpa only [hfunction] using hs
    · exact Helpers.callee_respects (fuel + 1) budget world guards callers function packets final packet cost hw hp hc hl
        (by simpa only [Ready, hi, Bool.false_eq_true, ite_false] using hd) (by simpa only [run, hi, Bool.false_eq_true, ite_false] using h)

def original (budget fuel : Nat) : Derived.Callees := run CallingCertificate.originalProgram.definitions budget fuel

theorem original_respects (budget fuel : Nat) :
    Derived.CallsRespect (original budget fuel) (SourceEval.run Certificate.original.body fuel)
      (Ready CallingCertificate.originalProgram.definitions budget fuel) :=
  run_respects _ CallingCertificate.original_codes budget fuel

theorem ready_noCalls (program : List TypeReader.Definition) (budget fuel : Nat) (world : World)
    (function : Function) (packets : List ValueCell) (hi : interpreted function = true)
    (hn : ∀ decl, program.find? (fun decl => decl.source.function == function) = some decl → Calling.noCalls decl.source.code = true) :
    Ready program budget (fuel + 1) world function packets := by
  simp only [Ready, hi, ite_true]
  intro decl hf callers
  exact Calling.readyFor_noCalls _ _ _ _ (hn decl hf) _ _

theorem ready_original_choice (budget fuel : Nat) (world : World) (packets : List ValueCell) :
    Ready CallingCertificate.originalProgram.definitions budget (fuel + 1) world .chooseLonger packets := by
  apply ready_noCalls _ budget fuel world .chooseLonger packets rfl
  intro decl hf
  rw [CallingCertificate.choice_lookup] at hf
  have he := Option.some.inj hf
  subst decl
  rw [CallingCertificate.originalChoice_spec.2.2]
  decide +kernel

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
