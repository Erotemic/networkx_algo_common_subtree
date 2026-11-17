module

public import SubtreeProofs.Rust.LookupRegionReader

/-! Structural coverage of region-use positions in retained signature/body
JSON. References and generic region arguments are checked at every descendant,
including unwind annotations. Declaration binders are checked separately. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader

open Lean Frontend

def roots (ctx : Frontend.Context) (json : Json) : Read (List Json) := do
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
    let function ← TypeReader.required (ctx.functions.lookup index)
    let actual ← array (← field (← field regular "generics") "regions")
    let expected := if function = .boxNew then 0 else Frontend.arity function
    if actual.length != expected then throw "callee region argument count mismatch"
  pure result

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
  inductive Tree (ctx : Frontend.Context) (scope : Scope) : Json → Prop where
    | node {json : Json} {raws : List Json} : roots ctx json = .ok raws → BoundRoots scope raws →
        Forest ctx scope (children json) → Tree ctx scope json

  inductive Forest (ctx : Frontend.Context) (scope : Scope) : List Json → Prop where
    | nil : Forest ctx scope []
    | cons {json : Json} {jsons : List Json} : Tree ctx scope json → Forest ctx scope jsons → Forest ctx scope (json :: jsons)
end

structure TreeCertificate (ctx : Frontend.Context) (scope : Scope) (json : Json) : Type where
  proof : Tree ctx scope json

structure ForestCertificate (ctx : Frontend.Context) (scope : Scope) (jsons : List Json) : Type where
  proof : Forest ctx scope jsons

mutual
  def scan (ctx : Frontend.Context) (scope : Scope) : Nat → (json : Json) → Read (TreeCertificate ctx scope json)
    | 0, _ => throw "region traversal budget exceeded"
    | fuel + 1, json =>
      match hr : roots ctx json with
      | .error message => throw message
      | .ok raws => do
        let bound ← boundRoots scope raws
        let rest ← scanForest ctx scope fuel (children json)
        pure ⟨.node hr bound rest.proof⟩
  termination_by fuel _ => fuel

  def scanForest (ctx : Frontend.Context) (scope : Scope) : Nat → (jsons : List Json) → Read (ForestCertificate ctx scope jsons)
    | 0, _ => throw "region traversal list budget exceeded"
    | _ + 1, [] => pure ⟨.nil⟩
    | fuel + 1, json :: jsons => do
      let first ← scan ctx scope fuel json
      let rest ← scanForest ctx scope fuel jsons
      pure ⟨.cons first.proof rest.proof⟩
  termination_by fuel _ => fuel
end

inductive Descendant : Json → Json → Prop where
  | refl (json : Json) : Descendant json json
  | child {root next target : Json} : next ∈ children root → Descendant next target → Descendant root target

def Mention (ctx : Frontend.Context) (root raw : Json) : Prop :=
  ∃ node raws, Descendant root node ∧ roots ctx node = .ok raws ∧ raw ∈ raws

theorem Forest.member {ctx : Frontend.Context} {scope : Scope} {jsons : List Json}
    (h : Forest ctx scope jsons) : ∀ json ∈ jsons, Tree ctx scope json :=
  match h with
  | .nil => by simp
  | .cons first rest => by
    intro json hm
    rcases List.mem_cons.mp hm with he | hm
    · subst json; exact first
    · exact rest.member json hm

theorem Tree.descendant {ctx : Frontend.Context} {scope : Scope} {root target : Json}
    (h : Tree ctx scope root) (hd : Descendant root target) : Tree ctx scope target := by
  induction hd with
  | refl => exact h
  | child hm _ ih => cases h with | node _ _ forest => exact ih (forest.member _ hm)

theorem Tree.mentions_bound {ctx : Frontend.Context} {scope : Scope} {root raw : Json}
    (h : Tree ctx scope root) (hm : Mention ctx root raw) : ∃ value, region scope raw = .ok value := by
  obtain ⟨node, raws, hd, hr, hm⟩ := hm
  have ht := h.descendant hd
  cases ht with
  | node hr' bounds _ =>
    rw [hr] at hr'
    cases hr'
    exact bounds.valid raw hm

end SubtreeProofs.Rust.LookupSource.Heap.Regions.Reader
