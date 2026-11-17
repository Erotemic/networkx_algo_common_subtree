module

public import SubtreeProofs.Rust.LookupSourceControl

/-! A normalized view retaining distinct source storage allocation and
deallocation instructions. Erasure recovers the existing exact-cost code. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Stack

inductive Code where
  | done
  | ret
  | step : Control.Action → Code → Code
  | branch : Scrutinee → Key → Option Key → Code → Code → Code → Code

def Code.erase : Code → LookupSource.Code
  | .done => .done
  | .ret => .ret
  | .step action rest => .step action.lower rest.erase
  | .branch scrut key other yes no rest => .branch scrut key other yes.erase no.erase rest.erase

def lower : Control.Block → Option Code
  | .done => some .done
  | .ret => some .ret
  | .step action rest => Code.step action <$> lower rest
  | .switch scrut cases fallback zero one rest => do
    let dispatch ← Control.lowerDispatch cases fallback
    let zero ← lower zero
    let one ← lower one
    let rest ← lower rest
    some (.branch scrut dispatch.key dispatch.other
      (if dispatch.swapped then one else zero) (if dispatch.swapped then zero else one) rest)

theorem lower_erases {source : Control.Block} {code : Code} (h : lower source = some code) :
    Control.lower source = some code.erase := by
  induction source generalizing code with
  | done => cases h; rfl
  | ret => cases h; rfl
  | step action rest ih =>
    cases hr : lower rest with
    | none => simp [lower, hr] at h
    | some next =>
      simp only [lower, hr] at h
      change some (Code.step action next) = some code at h
      cases h
      simp [Control.lower, ih hr, Code.erase]
  | switch scrut cases fallback zero one rest ihZero ihOne ihRest =>
    cases hd : Control.lowerDispatch cases fallback with
    | none => simp [lower, hd] at h
    | some dispatch =>
      cases hz : lower zero with
      | none => simp [lower, hd, hz] at h
      | some cz =>
        cases ho : lower one with
        | none => simp [lower, hd, hz, ho] at h
        | some co =>
          cases hr : lower rest with
          | none => simp [lower, hd, hz, ho, hr] at h
          | some cr =>
            simp only [lower, hd, hz, ho, hr, bind, Option.bind, Option.some.injEq] at h
            subst code
            cases hs : dispatch.swapped <;> simp [Control.lower, hd, ihZero hz, ihOne ho, ihRest hr, hs, Code.erase]

end SubtreeProofs.Rust.LookupSource.Stack
