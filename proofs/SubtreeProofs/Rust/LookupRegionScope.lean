module

public import SubtreeProofs.Rust.LookupRegionReader

/-! Structural coverage of region-use positions in retained signature/body
JSON. References and generic region arguments are checked at every descendant,
including unwind annotations. Declaration binders are checked separately. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader

open Lean Frontend

abbrev CalleeRegions := Nat → Read Nat

def calleeRegions (ctx : Frontend.Context) : CalleeRegions := fun index => do
  let function ← TypeReader.required (ctx.functions.lookup index)
  pure (if function = .boxNew then 0 else Frontend.arity function)

def rootsWith (arity : CalleeRegions) (json : Json) : Read (List Json) := do
  let mut result := []
  if let .ok untagged := field json "Untagged" then
    if let .ok ("Ref", payload) := tag untagged then
      match ← array payload with
      | [rawRegion, _, _] => result := [rawRegion]
      | _ => throw "invalid reference region position"
  if let .ok regions := field json "regions" then
    result := result ++ (← array regions)
  if let .ok call := field json "call" then
    let regular ← field (← field call "func") "Regular"
    let index ← (← field (← field regular "kind") "Fun").getNat?
    let actual ← array (← field (← field regular "generics") "regions")
    let expected ← arity index
    if actual.length != expected then throw "callee region argument count mismatch"
  pure result

def roots (ctx : Frontend.Context) : Json → Read (List Json) := rootsWith (calleeRegions ctx)

def children : Json → List Json
  | .arr values => values.toList
  | .obj fields => fields.toList.map Prod.snd
  | _ => []

structure BoundRoots (scope : Scope) (raws : List Json) : Type where
  valid : ∀ raw ∈ raws, ∃ value, region scope raw = .ok value

def boundRoots (scope : Scope) : (raws : List Json) → Read (BoundRoots scope raws)
  | [] => pure ⟨by simp⟩
  | raw :: raws =>
    match hr : region scope raw with
    | .error message => throw message
    | .ok value => do
      let rest ← boundRoots scope raws
      pure ⟨by
        intro item hm
        rcases List.mem_cons.mp hm with he | hm
        · subst item; exact ⟨value, hr⟩
        · exact rest.valid item hm⟩

mutual
  inductive TreeWith (arity : CalleeRegions) (scope : Scope) : Json → Prop where
    | node {json : Json} {raws : List Json} : rootsWith arity json = .ok raws → BoundRoots scope raws →
        ForestWith arity scope (children json) → TreeWith arity scope json

  inductive ForestWith (arity : CalleeRegions) (scope : Scope) : List Json → Prop where
    | nil : ForestWith arity scope []
    | cons {json : Json} {jsons : List Json} : TreeWith arity scope json → ForestWith arity scope jsons → ForestWith arity scope (json :: jsons)
end

structure TreeCertificateWith (arity : CalleeRegions) (scope : Scope) (json : Json) : Type where
  proof : TreeWith arity scope json

structure ForestCertificateWith (arity : CalleeRegions) (scope : Scope) (jsons : List Json) : Type where
  proof : ForestWith arity scope jsons

mutual
  def scanWith (arity : CalleeRegions) (scope : Scope) : Nat → (json : Json) → Read (TreeCertificateWith arity scope json)
    | 0, _ => throw "region traversal budget exceeded"
    | fuel + 1, json =>
      match hr : rootsWith arity json with
      | .error message => throw message
      | .ok raws => do
        let bound ← boundRoots scope raws
        let rest ← scanForestWith arity scope fuel (children json)
        pure ⟨.node hr bound rest.proof⟩
  termination_by fuel _ => fuel

  def scanForestWith (arity : CalleeRegions) (scope : Scope) : Nat → (jsons : List Json) → Read (ForestCertificateWith arity scope jsons)
    | 0, _ => throw "region traversal list budget exceeded"
    | _ + 1, [] => pure ⟨.nil⟩
    | fuel + 1, json :: jsons => do
      let first ← scanWith arity scope fuel json
      let rest ← scanForestWith arity scope fuel jsons
      pure ⟨.cons first.proof rest.proof⟩
  termination_by fuel _ => fuel
end

inductive Descendant : Json → Json → Prop where
  | refl (json : Json) : Descendant json json
  | child {root next target : Json} : next ∈ children root → Descendant next target → Descendant root target

def MentionWith (arity : CalleeRegions) (root raw : Json) : Prop :=
  ∃ node raws, Descendant root node ∧ rootsWith arity node = .ok raws ∧ raw ∈ raws

theorem ForestWith.member {arity : CalleeRegions} {scope : Scope} {jsons : List Json}
    (h : ForestWith arity scope jsons) : ∀ json ∈ jsons, TreeWith arity scope json :=
  match h with
  | .nil => by simp
  | .cons first rest => by
    intro json hm
    rcases List.mem_cons.mp hm with he | hm
    · subst json; exact first
    · exact rest.member json hm

theorem TreeWith.descendant {arity : CalleeRegions} {scope : Scope} {root target : Json}
    (h : TreeWith arity scope root) (hd : Descendant root target) : TreeWith arity scope target := by
  induction hd with
  | refl => exact h
  | child hm _ ih => cases h with | node _ _ forest => exact ih (forest.member _ hm)

theorem TreeWith.mentions_bound {arity : CalleeRegions} {scope : Scope} {root raw : Json}
    (h : TreeWith arity scope root) (hm : MentionWith arity root raw) : ∃ value, region scope raw = .ok value := by
  obtain ⟨node, raws, hd, hr, hm⟩ := hm
  have ht := h.descendant hd
  cases ht with
  | node hr' bounds _ =>
    rw [hr] at hr'
    cases hr'
    exact bounds.valid raw hm

abbrev Tree (ctx : Frontend.Context) := TreeWith (calleeRegions ctx)
abbrev Forest (ctx : Frontend.Context) := ForestWith (calleeRegions ctx)
abbrev TreeCertificate (ctx : Frontend.Context) := TreeCertificateWith (calleeRegions ctx)
abbrev ForestCertificate (ctx : Frontend.Context) := ForestCertificateWith (calleeRegions ctx)
def scan (ctx : Frontend.Context) := scanWith (calleeRegions ctx)
def scanForest (ctx : Frontend.Context) := scanForestWith (calleeRegions ctx)
abbrev Mention (ctx : Frontend.Context) := MentionWith (calleeRegions ctx)

theorem Forest.member {ctx : Frontend.Context} {scope : Scope} {jsons : List Json}
    (h : Forest ctx scope jsons) : ∀ json ∈ jsons, Tree ctx scope json := ForestWith.member h

theorem Tree.descendant {ctx : Frontend.Context} {scope : Scope} {root target : Json}
    (h : Tree ctx scope root) (hd : Descendant root target) : Tree ctx scope target := TreeWith.descendant h hd

theorem Tree.mentions_bound {ctx : Frontend.Context} {scope : Scope} {root raw : Json}
    (h : Tree ctx scope root) (hm : Mention ctx root raw) : ∃ value, region scope raw = .ok value :=
  TreeWith.mentions_bound h hm

end SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader
