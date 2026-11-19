import SubtreeProofs.Rust.SourceEvalRegionCertificate
import SubtreeProofs.Rust.LookupRegionSemantics

open Lean SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource SubtreeProofs.Rust.LookupSource.Heap

-- The actual evaluator has three value inputs and two signature lifetimes;
-- insertion has four values/three lifetimes and owned choice has no lifetime.
example : SourceEval.arity .evaluate = 3 ∧ SourceEval.Regions.regionArity .evaluate = 2 := ⟨rfl, rfl⟩
example : SourceEval.arity .insert = 4 ∧ SourceEval.Regions.regionArity .insert = 3 := ⟨rfl, rfl⟩
example : SourceEval.Regions.regionArity .chooseLonger = 0 := rfl

example : ∃ program, SourceEval.Regions.read SourceEval.Input.Program.source = .ok program ∧
    ∃ decl ∈ program.definitions, decl.function = .evaluate ∧
      decl.source.source.code = SourceEval.Certificate.original.body .evaluate ∧ decl.freeCount = 2 := by
  obtain ⟨program, hr, hp⟩ := SourceEval.Regions.Certificate.original_program
  exact ⟨program, hr, hp .evaluate (by decide +kernel)⟩

private def ctx : TypeReader.Context :=
  ⟨⟨[(1, .word), (2, .table), (3, .entry), (4, .embedding), (5, .optional), (6, .tuple)], [], 0⟩, 7⟩
private def scalarOption : Json := json% {"Untagged":{"Adt":{"id":5,"builtin":null,
  "generics":{"regions":[],"types":[{"Untagged":{"Scalar":{"Integer":{"Unsigned":"U32"}}}}],
  "const_generics":[],"trait_refs":[]}}}}

-- The shared regional reader now attaches the actual scalar-option local type.
example : (Regions.Reader.annotation ctx (.body 0) scalarOption).isOk = true := by decide +kernel

private def info : SourceEval.ProgramReader.ContextInfo :=
  ⟨ctx.source, [(10, .evaluate), (11, .chooseLonger), (12, .checkedAdd), (13, .insert)], [], []⟩
private def rejected (value : Except String α) : Bool :=
  match value with | .error _ => true | .ok _ => false
private def call (index : Nat) (regions : List Json) : Json := json% {
  "call":{"func":{"Regular":{"kind":{"Fun":$(index)},"generics":{"regions":$(regions)}}}}}

-- A value-arity shortcut would accept the wrong evaluator instance. Nested
-- traversal also checks the actual region indices, including unwind metadata.
example : rejected (Regions.Reader.rootsWith (SourceEval.Regions.calleeRegions info)
    (call 10 [json% {"Body":0}, json% {"Body":1}, json% {"Body":2}])) = true := by decide +kernel
example : (Regions.Reader.scanWith (SourceEval.Regions.calleeRegions info) (.body 2) 64
    (call 10 [json% {"Body":0}, json% {"Body":1}])).isOk = true := by decide +kernel
example : rejected (Regions.Reader.scanWith (SourceEval.Regions.calleeRegions info) (.body 2) 64
    (json% {"on_unwind":$(call 10 [json% {"Body":0}, json% {"Body":9}])})) = true := by decide +kernel
example : (Regions.Reader.rootsWith (SourceEval.Regions.calleeRegions info) (call 11 [])).isOk = true := by decide +kernel
example : (Regions.Reader.rootsWith (SourceEval.Regions.calleeRegions info) (call 12 [])).isOk = true := by decide +kernel
example : rejected (Regions.Reader.rootsWith (SourceEval.Regions.calleeRegions info)
    (call 13 [json% {"Body":0}, json% {"Body":1}, json% {"Body":2}, json% {"Body":3}])) = true := by decide +kernel

-- The option extension preserves the existing region erasure interpretation.
example : Regions.Value [] [] (fun _ _ => False) (.node .optional 1 [.number 7]) (.option .u32) :=
  .optionSome (.number (by decide +kernel))

example : Regions.Scoped (.body 10) (.option (.shared (.body 9) (.adt .word))) :=
  .option (.shared (by change 9 < 10; decide +kernel) (.adt .word))
example (base current : Memory) (pointer : Pointer) :
    ¬ Regions.Value base current (fun _ _ => False) (.node .optional 1 [.shared pointer])
      (.option (.shared (.body 9) (.adt .word))) := by
  intro h
  cases h with | optionSome child => cases child with | shared _ _ hlive _ => cases hlive
