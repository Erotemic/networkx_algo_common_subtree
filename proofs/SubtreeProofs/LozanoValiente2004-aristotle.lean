/-
  Sketch formalization of:
    Lozano & Valiente (2004) "On the maximum common embedded subtree problem for ordered trees."

  This file is intentionally definition-heavy and proof-light (lots of `sorry`).
  The goal is to lock down the *definitions* and the key *theorem statements*
  so we can validate the spec before proving anything.

  Notes on notation:
  * The paper uses 0/1 for parentheses; Mathlib uses `DyckStep.U` / `DyckStep.D`.
    We interpret U as “0 / open” and D as “1 / close”.
  * The paper’s containment symbol is sometimes read in the opposite direction in the literature.
    Here we use `r ⊑ p` to mean: “r is contained in p”, i.e. p can be reduced to r by deletions.

  Future extension hook (Option A):
  * When we later add labels/weights to parentheses, we will keep an underlying `DyckWord` “shape”
    and carry annotations separately (e.g. `ann : Fin shape.semilength → σ`).
-/

import Mathlib
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.Nat.Find

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

namespace LozanoValiente


open DyckStep

/-! ## 1) Balanced sequences as `DyckWord` -/

/-- Paper “balanced sequence” type. -/
abbrev BSeq : Type := DyckWord

namespace BSeq

/-- Semilength: number of matched pairs (paper: m edges ↔ 2m symbols). -/
abbrev semilen (s : BSeq) : Nat := s.semilength

/-- Empty balanced sequence. -/
abbrev empty : BSeq := (0 : DyckWord)

/-- Paper’s `head(s)` (inside of the first matching pair).  Defined for all `DyckWord`s;
    for `0` it is `0`. -/
abbrev head (s : BSeq) : BSeq := s.insidePart

/-- Paper’s `tail(s)` (remainder after the first matching pair).  Defined for all `DyckWord`s;
    for `0` it is `0`. -/
abbrev tail (s : BSeq) : BSeq := s.outsidePart

/-- Paper’s `head(s) · tail(s)` (delete the outermost matched pair). -/
abbrev headTail (s : BSeq) : BSeq := s.insidePart + s.outsidePart

/-!
  Decomposition set `decomp(s)` (paper Definition 4):
  closure under taking `head`, `tail`, and `headTail` starting from `s`.

  (We model it as an inductive reachability predicate; later we can add a computable `Finset`.)
-/

inductive DecompMem : BSeq → BSeq → Prop
| base  (s : BSeq) : DecompMem s s
| head  (s t : BSeq) : DecompMem s t → DecompMem s (head t)
| tail  (s t : BSeq) : DecompMem s t → DecompMem s (tail t)
| htail (s t : BSeq) : DecompMem s t → DecompMem s (headTail t)

/-- `decompSet s` is the set `{ t | t ∈ decomp(s) }`. -/
def decompSet (s : BSeq) : Set BSeq := { t | DecompMem s t }

theorem decompSet_contains_self (s : BSeq) : s ∈ decompSet s := by
  exact DecompMem.base s

/-!
  Deletion relation.

  In the paper, deletions are described as deleting “edge annotations” (matched 0…1 pairs)
  from the balanced sequence.

  We make the intent explicit and name this `DelAnyAnnot`:
  *single-step deletion of any matched pair anywhere*.

  DyckWord form:
    t = a + nest(b) + c   and   s = a + b + c

  where `nest(b)` is `U :: b ++ [D]` (i.e. wrap by a matched pair).
-/

def DelAnyAnnot (t s : BSeq) : Prop :=
  ∃ a b c : BSeq,
    t = a + b.nest + c ∧
    s = a + b + c

/-!
### Basic semilength facts for deletions

These are “easy” lemmas that we will reuse frequently:

* A single deletion (`DelAnyAnnot`) reduces semilength by exactly 1.
* Therefore, reachability by deletions (`⊑`) can only reduce semilength.

They follow immediately from Mathlib's simp lemmas
`DyckWord.semilength_add` and `DyckWord.semilength_nest`.
-/

theorem semilen_of_delAnyAnnot {t s : BSeq} (h : DelAnyAnnot t s) :
    semilen s + 1 = semilen t := by
  rcases h with ⟨a, b, c, ht, hs⟩
  subst ht
  subst hs
  -- Now everything is arithmetic over `DyckWord.semilength`.
  -- `simp` uses `DyckWord.semilength_add` and `DyckWord.semilength_nest`.
  simp [semilen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Containment: `r ⊑ p` means `r` is obtainable from `p` by repeated deletions.

  We define it as a reflexive-transitive closure, so `p ⊑ p` holds automatically.
-/
def ContainedIn (r p : BSeq) : Prop :=
  Relation.ReflTransGen DelAnyAnnot p r

infix:50 " ⊑ " => ContainedIn

/-- A single deletion can only (strictly) decrease semilength. -/
theorem semilen_le_of_delAnyAnnot {t s : BSeq} (h : DelAnyAnnot t s) :
    semilen s ≤ semilen t := by
  have eq : semilen s + 1 = semilen t := semilen_of_delAnyAnnot h
  have lt : semilen s < semilen t := by
    simpa [eq] using (Nat.lt_succ_self (semilen s))
  exact Nat.le_of_lt lt

theorem semilen_le_of_containedIn {r p : BSeq} (h : r ⊑ p) : semilen r ≤ semilen p := by
  -- Induction on the deletion chain `p ⇒* r`.
  -- (We spell out binder names to avoid relying on `rename_i` heuristics.)
  induction h with
  | refl =>
      simp [semilen]
  | tail hab hstep ih =>
      -- hab : p ⇒* b, ih : semilen b ≤ semilen p
      -- hstep : b ⇒ r, so semilen r ≤ semilen b
      exact le_trans (semilen_le_of_delAnyAnnot hstep) ih

/-!
  LCBS spec (Longest Common Balanced Sequence).

  `r` is an LCBS of `p,q` if:
  * `r` is contained in both `p` and `q`, and
  * `r` has maximal semilength among all common contained sequences.

  (The paper proves this corresponds to MCES on trees after encoding.)
-/

def IsLCBS (r p q : BSeq) : Prop :=
  r ⊑ p ∧ r ⊑ q ∧
  ∀ r', r' ⊑ p → r' ⊑ q → semilen r' ≤ semilen r

/-!
  A small but useful lemma: every Dyck word can be reduced to `0` by repeated deletions.

  Intuition: if `p ≠ 0`, Mathlib's decomposition lemma
  `DyckWord.nest_insidePart_add_outsidePart` says

  `p = p.insidePart.nest + p.outsidePart`.

  Deleting the outermost pair produces `p.insidePart + p.outsidePart = headTail p`.
  Repeating strictly decreases `semilen` until we reach `0`.
-/

theorem del_headTail_of_ne_zero (p : BSeq) (hp : p ≠ 0) : DelAnyAnnot p (headTail p) := by
  refine ⟨0, head p, tail p, ?_, ?_⟩
  · -- `p = 0 + (head p).nest + tail p`
    -- Mathlib: `p.insidePart.nest + p.outsidePart = p` for `p ≠ 0`.
    -- Note: `head p = p.insidePart`, `tail p = p.outsidePart`.
    simpa [head, tail] using (DyckWord.nest_insidePart_add_outsidePart (p := p) hp).symm
  · -- `headTail p = 0 + head p + tail p`
    simp [headTail, head, tail]


/-- Well-foundedness of the strict `Nat` measure `f`. (Compat shim: `measure_wf` used to be in Std/Mathlib.) -/
theorem measure_wf {γ : Sort _} (f : γ → Nat) :
    WellFounded (fun a b : γ => f a < f b) := by
  classical
  let r : γ → γ → Prop := fun a b => f a < f b
  refine ⟨?acc⟩
  intro a

  -- accessibility of the measure in Nat
  have hNat : Acc (fun m n : Nat => m < n) (f a) :=
    (Nat.lt_wfRel.wf).apply (f a)

  -- lift accessibility along the measure
  have lift :
      ∀ {n : Nat},
        Acc (fun m n : Nat => m < n) n →
        ∀ {a : γ}, f a = n → Acc r a := by
    intro n hn
    induction hn with
    | intro n hn ih =>
        intro a ha
        refine Acc.intro a ?_
        intro b hb
        have hbn : f b < n := by simpa [r, ha] using hb
        -- `a` is implicit for `ih`, so pass it explicitly:
        exact ih (f b) hbn (a := b) rfl

  exact lift hNat rfl

theorem zero_containedIn (p : BSeq) : (0 : BSeq) ⊑ p := by
  classical
  -- Well-founded induction on `semilen`.
  refine (measure_wf semilen).induction p ?_
  intro p ih
  by_cases hp : p = 0
  · subst hp
    exact Relation.ReflTransGen.refl
  ·
    have hstep : DelAnyAnnot p (headTail p) := del_headTail_of_ne_zero p hp
    have hlt : semilen (headTail p) < semilen p := by
      have heq : semilen (headTail p) + 1 = semilen p := semilen_of_delAnyAnnot hstep
      -- Convert `x + 1 = y` into `x < y`.
      exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self (semilen (headTail p))) heq
    -- Chain: p ⇒ headTail p ⇒* 0
    have hph : Relation.ReflTransGen DelAnyAnnot p (headTail p) :=
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep
    have hto0 : Relation.ReflTransGen DelAnyAnnot (headTail p) 0 := ih (headTail p) hlt
    exact Relation.ReflTransGen.trans hph hto0

theorem exists_LCBS (p q : BSeq) : ∃ r : BSeq, IsLCBS r p q := by
  -- finiteness / well-foundedness argument (bounded by semilen)
  -- By definition of LCBS, such an r exists.
  have h_exists_lCBS : ∃ r, ContainedIn r p ∧ ContainedIn r q := by
    -- The empty sequence is contained in any sequence, so we can take r to be the empty sequence.
    use 0;
    -- The empty sequence is contained in any sequence by definition.
    have h_empty_contained : ∀ p : BSeq, ContainedIn 0 p := by
      intro p
      induction' p using DyckWord.recOn with p ih;
      -- By repeatedly applying the deletion operation, we can reduce any Dyck word to the empty word.
      have h_deletion : ∀ p : DyckWord, ContainedIn 0 p := by
        intro p
        induction' p using DyckWord.recOn with p ih;
        -- By repeatedly applying the deletion operation, we can reduce any Dyck word to the empty word. Each deletion step reduces the semilength by 1.
        have h_deletion_step : ∀ p : DyckWord, p ≠ 0 → ∃ q : DyckWord, DelAnyAnnot p q ∧ BSeq.semilen q < BSeq.semilen p := by
          intro p hp_nonzero
          obtain ⟨a, b, c, hp⟩ : ∃ a b c : BSeq, p = a + b.nest + c := by
            use 0, p.insidePart, p.outsidePart;
            -- By definition of DyckWord, we can write p as the concatenation of its inside part, the nested part, and the outside part.
            have h_decomp : p = p.insidePart.nest + p.outsidePart := by
              exact?;
            simpa using h_decomp;
          use a + b + c;
          -- By definition of DelAnyAnnot, we have that p = a + b.nest + c and s = a + b + c.
          simp [hp, DelAnyAnnot];
          exact ⟨ a, b, c, rfl, rfl ⟩;
        -- By repeatedly applying the deletion operation, we can reduce any Dyck word to the empty word. Each deletion step reduces the semilength by 1, so we can apply induction on the semilength.
        have h_induction : ∀ n : ℕ, ∀ p : DyckWord, BSeq.semilen p = n → ContainedIn 0 p := by
          intro n p hp
          induction' n using Nat.strong_induction_on with n ih generalizing p;
          by_cases hp_zero : p = 0;
          · exact hp_zero.symm ▸ Relation.ReflTransGen.refl;
          · obtain ⟨ q, hq₁, hq₂ ⟩ := h_deletion_step p hp_zero;
            exact Relation.ReflTransGen.head hq₁ ( ih _ ( by linarith ) _ rfl );
        exact h_induction _ _ rfl;
      exact h_deletion _
    exact ⟨h_empty_contained p, h_empty_contained q⟩;
  -- By definition of LCBS, such an r exists because the set of common subsequences is finite.
  obtain ⟨r, hr⟩ : ∃ r ∈ {r | ContainedIn r p ∧ ContainedIn r q}, ∀ s ∈ {r | ContainedIn r p ∧ ContainedIn r q}, BSeq.semilen s ≤ BSeq.semilen r := by
    -- Apply the well-ordering principle to the set {r | ContainedIn r p ∧ ContainedIn r q}.
    apply Classical.byContradiction
    intro h_no_max;
    -- Apply the well-ordering principle to the set of semilengths of common subsequences.
    obtain ⟨m, hm⟩ : ∃ m ∈ Set.image BSeq.semilen {r | ContainedIn r p ∧ ContainedIn r q}, ∀ n ∈ Set.image BSeq.semilen {r | ContainedIn r p ∧ ContainedIn r q}, n ≤ m := by
      apply_rules [ Set.exists_max_image ];
      · exact Set.finite_iff_bddAbove.mpr ⟨ p.semilen, Set.forall_mem_image.mpr fun r hr => semilen_le_of_containedIn hr.1 ⟩;
      · exact ⟨ _, ⟨ h_exists_lCBS.choose, h_exists_lCBS.choose_spec, rfl ⟩ ⟩;
    obtain ⟨ ⟨ r, hr, rfl ⟩, hm ⟩ := hm; exact h_no_max ⟨ r, hr, fun s hs => hm _ <| Set.mem_image_of_mem _ hs ⟩ ;
  exact ⟨ r, hr.1.1, hr.1.2, fun s hs hs' => hr.2 s ⟨ hs, hs' ⟩ ⟩
noncomputable def LCBS (p q : BSeq) : BSeq :=
  Classical.choose (exists_LCBS p q)

theorem LCBS_spec (p q : BSeq) : IsLCBS (LCBS p q) p q := by
  classical
  simpa [LCBS] using Classical.choose_spec (exists_LCBS p q)

/-- Length of LCBS in semilength units. -/
noncomputable def lcsLen (p q : BSeq) : Nat := semilen (LCBS p q)

end BSeq

/-! ## 2) Ordered rooted trees and embedded-subtree relation via edge contraction -/
universe u v

/-- Rooted ordered trees with node labels `α` and edge labels `β` (children are ordered). -/
inductive OTree (α : Type u) (β : Type v) : Type (max u v)
| node (a : α) (children : List (β × OTree α β))
deriving Repr

namespace OTree

variable {α : Type u} {β : Type v}


/-- Root label of an `OTree`. -/
def root : OTree α β → α
| .node a _ => a

/-- Children (edge label × subtree) list of an `OTree`. -/
def children : OTree α β → List (β × OTree α β)
| .node _ cs => cs

@[simp] theorem root_node (a : α) (cs : List (β × OTree α β)) : root (.node a cs) = a := rfl
@[simp] theorem children_node (a : α) (cs : List (β × OTree α β)) : children (.node a cs) = cs := rfl

mutual
  /-- Edge count (paper's size measure is number of edges). -/
  def edgeCount {α : Type u} {β : Type v} : OTree α β → Nat
  | .node _ cs => cs.length + edgeCountChildren cs

  def edgeCountChildren {α : Type u} {β : Type v} :
      List (β × OTree α β) → Nat
  | [] => 0
  | (_, t) :: rest => edgeCount t + edgeCountChildren rest
end

/-- Contract the edge to the i-th child at the root by splicing that child's children
    into the parent's children list at position i (preserving order). -/
def contractAtRoot : OTree α β → Nat → Option (OTree α β)
| .node a cs, i =>
    match cs.splitAt i with
    | (_, []) => none
    | (before, (_lbl, child) :: after) =>
        match child with
        | .node _ childCs =>
            some (.node a (before ++ childCs ++ after))

/-- One-step contraction anywhere in the tree (root contraction, or descend and contract inside a child). -/
inductive Contract1 : OTree α β → OTree α β → Prop
| root {t t' : OTree α β} {i : Nat} (h : contractAtRoot t i = some t') :
    Contract1 t t'
| inChild {a : α} {cs : List (β × OTree α β)} {i : Nat}
    {before after : List (β × OTree α β)}
    {lbl : β} {child child' : OTree α β}
    (hsplit : cs.splitAt i = (before, (lbl, child) :: after))
    (hrec   : Contract1 child child') :
    Contract1 (.node a cs) (.node a (before ++ (lbl, child') :: after))

/-- Embedded subtree: `t ≼ s` if `s` can be contracted to `t`. -/
def Embeds (t s : OTree α β) : Prop :=
  Relation.ReflTransGen Contract1 s t

infix:50 " ≼ " => Embeds

/-- `t` is a common embedded subtree of `s1,s2`. -/
def IsCommonEmbedded (t s1 s2 : OTree α β) : Prop := (t ≼ s1) ∧ (t ≼ s2)

/-- Maximum common embedded subtree (MCES), by edge-count maximality. -/
def IsMCES (t s1 s2 : OTree α β) : Prop :=
  IsCommonEmbedded t s1 s2 ∧
  ∀ t', IsCommonEmbedded t' s1 s2 → edgeCount t' ≤ edgeCount t


theorem exists_MCES {α : Type u} {β : Type v} (s1 s2 : OTree α β)
    (h : s1.root = s2.root) : ∃ t : OTree α β, IsMCES t s1 s2 := by
  classical
  sorry

theorem edgeCountChildren_append {α : Type u} {β : Type v} :
    ∀ (xs ys : List (β × OTree α β)),
      edgeCountChildren (xs ++ ys) = edgeCountChildren xs + edgeCountChildren ys
  | [], ys => by simp [edgeCountChildren]
  | (x :: xs), ys => by
      cases x with
      | mk lbl t =>
        simp [edgeCountChildren, edgeCountChildren_append xs ys, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem edgeCountChildren_before_cons_after {α : Type u} {β : Type v}
    (before : List (β × OTree α β)) (lbl : β) (child : OTree α β) (after : List (β × OTree α β)) :
    edgeCountChildren (before ++ (lbl, child) :: after)
      = edgeCountChildren before + edgeCount child + edgeCountChildren after := by
  induction before with
  | nil =>
      simp [edgeCountChildren]
  | cons x xs ih =>
      cases x with
      | mk lblx tx =>
        simp [edgeCountChildren, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem contract1_decreases_edgeCount {α : Type u} {β : Type v} {t s : OTree α β}
    (h : Contract1 s t) :
    OTree.edgeCount s = OTree.edgeCount t + 1 := by
  classical
  -- A small helper: the pieces returned by `splitAt` append back to the original list.
  -- (In this Mathlib snapshot, `simp` rewrites `splitAt` to `take/drop`.)
  have splitAt_fst_append_snd {δ : Type _} (cs : List δ) (i : Nat) :
      (cs.splitAt i).1 ++ (cs.splitAt i).2 = cs := by
    simpa using (List.take_append_drop i cs)

  induction h with
  | root hcontract =>
      rename_i i
      cases s with
      | node a cs =>
          cases hsplit : cs.splitAt i with
          | mk before rest =>
              cases rest with
              | nil =>
                  -- `contractAtRoot` returns `none` here, contradicting `some _`
                  have hc := hcontract
                  simp [contractAtRoot, hsplit] at hc
                  cases hc
              | cons p after =>
                  cases p with
                  | mk lbl child =>
                      cases child with
                      | node ach childCs =>
                          -- identify the contracted result `t`
                          have hc := hcontract
                          simp [contractAtRoot, hsplit] at hc
                          cases hc

                          -- recover `cs = before ++ (lbl, node ach childCs) :: after`
                          have hcs : cs = before ++ (lbl, OTree.node ach childCs) :: after := by
                            have hcat :
                                (cs.splitAt i).1 ++ (cs.splitAt i).2 =
                                  before ++ (lbl, OTree.node ach childCs) :: after := by
                              simpa using (congrArg (fun q => q.1 ++ q.2) hsplit)
                            have hsplitcat : (cs.splitAt i).1 ++ (cs.splitAt i).2 = cs :=
                              splitAt_fst_append_snd cs i
                            exact hsplitcat.symm.trans hcat

                          -- compute edge counts; one contraction removes exactly one edge
                          simp [OTree.edgeCount, OTree.edgeCountChildren, hcs,
                                edgeCountChildren_before_cons_after, edgeCountChildren_append,
                                List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                          ring_nf
  | inChild hsplit hrec ih =>
      rename_i a cs i before after lbl child child'
      -- recover `cs = before ++ (lbl, child) :: after`
      have hcs : cs = before ++ (lbl, child) :: after := by
        have hcat :
            (cs.splitAt i).1 ++ (cs.splitAt i).2 =
              before ++ (lbl, child) :: after := by
          simpa using (congrArg (fun q => q.1 ++ q.2) hsplit)
        have hsplitcat : (cs.splitAt i).1 ++ (cs.splitAt i).2 = cs :=
          splitAt_fst_append_snd cs i
        exact hsplitcat.symm.trans hcat

      -- only the contracted child changes, by IH
      simp [OTree.edgeCount, OTree.edgeCountChildren, hcs,
            edgeCountChildren_before_cons_after, ih,
            List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      ring_nf


noncomputable def MCES (s1 s2 : OTree α β) (h : s1.root = s2.root) : OTree α β :=
  Classical.choose (exists_MCES (s1 := s1) (s2 := s2) h)

theorem MCES_spec (s1 s2 : OTree α β) (h : s1.root = s2.root) :
    IsMCES (MCES s1 s2 h) s1 s2 := by
  classical
  simpa [MCES] using Classical.choose_spec (exists_MCES (s1 := s1) (s2 := s2) h)


end OTree

/-! ## 3) Encoding trees as balanced sequences (paper Definition 1) -/

namespace Encoding

open BSeq
open OTree

variable {α : Type u} {β : Type v}

/-
  Paper encoding b(t):
    leaf -> ε
    node with children t₁..tₖ -> 0 b(t₁) 1 ... 0 b(tₖ) 1

  In DyckWord terms, this is: fold over children, appending `nest(encode child)`.
-/

mutual
  def encode : OTree α β → BSeq
  | .node _ cs => encodeChildren cs

  def encodeChildren : List (β × OTree α β) → BSeq
  | [] => 0
  | (_, t) :: rest => (encode t).nest + encodeChildren rest
end

/-!
  Key size fact (paper): `semilen (encode t) = edgeCount t`.

  Because both `encode` and `edgeCount` are defined mutually over trees and child-lists,
  the cleanest proof is also mutual:

  * for a child-list `cs`, `semilen (encodeChildren cs) = cs.length + edgeCountChildren cs`
    (each child contributes its own edges plus the one edge from its parent), and
  * for a node, this list lemma directly yields the node lemma.

  This avoids relying on the somewhat awkward automatically-generated recursor for `OTree`
  (whose induction hypothesis is packaged in a way that is easy to get wrong).
-/

mutual

  theorem semilen_encode_eq_edgeCount :
      ∀ t : OTree α β, BSeq.semilen (encode t) = OTree.edgeCount t
  | .node _ cs => by
      simpa [encode, OTree.edgeCount] using
        (semilen_encodeChildren_eq_edgeCountChildren cs)

  -- termination_by
  --   (OTree.edgeCount t, (1 : Nat))
  -- decreasing_by
  --   simp_wf

  theorem semilen_encodeChildren_eq_edgeCountChildren :
      ∀ cs : List (β × OTree α β),
        BSeq.semilen (encodeChildren cs) = cs.length + OTree.edgeCountChildren cs
  | [] => by
      simp [encodeChildren, OTree.edgeCountChildren, BSeq.semilen]
  | (_, t) :: rest => by
      have ht : BSeq.semilen (encode t) = OTree.edgeCount t :=
        semilen_encode_eq_edgeCount t
      have hrest :
          BSeq.semilen (encodeChildren rest) = rest.length + OTree.edgeCountChildren rest :=
        semilen_encodeChildren_eq_edgeCountChildren rest
      simp [encodeChildren, OTree.edgeCountChildren, BSeq.semilen, ht, hrest,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  -- termination_by
  --   (cs.length + OTree.edgeCountChildren cs, (0 : Nat))
  -- decreasing_by
  --   simp_wf

end

/-!
  Bridge between tree contractions and Dyck deletions.

  This is the central correctness interface between the tree world and the Dyck world.
  For the companion proof to the paper, these are the “unit tests” that ensure we are
  formalizing the same object.
-/

/-- One-step contraction implies one-step deletion on encodings. -/
theorem contract1_implies_delAnyAnnot
    {t t' : OTree α β} (h : OTree.Contract1 t t') :
    BSeq.DelAnyAnnot (encode t) (encode t') := by
  sorry

/-- Embedding (multi-step contractions) implies containment (multi-step deletions). -/
theorem embeds_implies_contained
    {t s : OTree α β} (h : t ≼ s) :
    (encode t) ⊑ (encode s) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hab hstep ih =>
      exact Relation.ReflTransGen.tail ih (contract1_implies_delAnyAnnot hstep)
    /-- (Optional but convenient) For an encoding `encode s`, containment implies there exists
    an embedded subtree whose encoding is exactly the contained word.

    This is the direction that typically uses a decoder/parser.
-/
theorem contained_implies_exists_embedded_with_encoding
    {s : OTree α β} {r : BSeq} (h : r ⊑ (encode s)) :
    ∃ t : OTree α β, t ≼ s ∧ encode t = r := by
  sorry

end Encoding

/-! ## 4) Main equivalence: LCBS of encodings corresponds to MCES -/

namespace MainTheorem

open BSeq
open OTree
open Encoding

variable {α : Type u} {β : Type v}

/-- If `t` is an MCES, then `encode t` is an LCBS of `encode s1` and `encode s2`. -/
theorem mces_encoding_is_lcbs
    (s1 s2 : OTree α β) (h : s1.root = s2.root) :
    IsLCBS (encode (MCES s1 s2 h)) (encode s1) (encode s2) := by
  -- 1) MCES gives maximal edgeCount among common embedded subtrees
  -- 2) semilen_encode_eq_edgeCount transfers maximality to semilength
  -- 3) embeds_implies_contained gives containment
  -- 4) conclude LCBS maximality
  sorry

/-- Conversely, an LCBS corresponds to some maximum common embedded subtree. -/
theorem lcbs_corresponds_to_mces
    (s1 s2 : OTree α β) :
    ∃ t : OTree α β,
      IsMCES t s1 s2 ∧
      encode t = LCBS (encode s1) (encode s2) := by
  -- Use contained_implies_exists_embedded_with_encoding twice, then maximality of LCBS,
  -- then semilen_encode_eq_edgeCount.
  sorry

/-- The main numeric equality (paper Theorem 2-ish): sizes match. -/
theorem mces_size_eq_lcbs_len
    (s1 s2 : OTree α β) (h : s1.root = s2.root) :
    OTree.edgeCount (MCES s1 s2 h) = BSeq.lcsLen (encode s1) (encode s2) := by
  -- from mces_encoding_is_lcbs and semilen_encode_eq_edgeCount
  sorry

end MainTheorem

/-! ## 5) Lemma 8 recurrence for LCBS length (paper Lemma 8) -/

namespace Recurrence

open BSeq

/-- Base cases. -/
theorem lcsLen_empty_left (t : BSeq) :
    lcsLen 0 t = 0 := by
  classical
  -- Let `r = LCBS 0 t`. Since `r ⊑ 0`, semilength cannot exceed `semilen 0 = 0`.
  have hspec := (LCBS_spec (p := (0 : BSeq)) (q := t))
  have hcont : (LCBS (0 : BSeq) t) ⊑ (0 : BSeq) := hspec.1
  have hle : semilen (LCBS (0 : BSeq) t) ≤ semilen (0 : BSeq) :=
    semilen_le_of_containedIn hcont
  have hzero : semilen (LCBS (0 : BSeq) t) = 0 := by
    -- `semilen 0 = 0` is `DyckWord.semilength_zero`.
    exact Nat.eq_zero_of_le_zero (by simpa [semilen] using hle)
  simpa [lcsLen, hzero]

theorem lcsLen_empty_right (s : BSeq) :
    lcsLen s 0 = 0 := by
  classical
  have hspec := (LCBS_spec (p := s) (q := (0 : BSeq)))
  have hcont : (LCBS s (0 : BSeq)) ⊑ (0 : BSeq) := hspec.2.1
  have hle : semilen (LCBS s (0 : BSeq)) ≤ semilen (0 : BSeq) :=
    semilen_le_of_containedIn hcont
  have hzero : semilen (LCBS s (0 : BSeq)) = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [semilen] using hle)
  simpa [lcsLen, hzero]

/-!
  Lemma 8 recurrence, stated using Mathlib's `insidePart/outsidePart`.

  In Mathlib, `insidePart` and `outsidePart` are defined for *all* Dyck words;
  the lemma is meaningful (and typically proved) under `s ≠ 0` and `t ≠ 0`.

  Paper statement (informal): for nonempty balanced sequences s,t:

    lcs(s,t) = max(
      lcs(head(s), head(t)) + lcs(tail(s), tail(t)) + 1,
      lcs(headTail(s), t),
      lcs(s, headTail(t))
    )
-/

theorem lemma8_recurrence
    (s t : BSeq) (hs : s ≠ 0) (ht : t ≠ 0) :
    lcsLen s t =
      Nat.max
        (Nat.max
          (lcsLen (head s) (head t) + lcsLen (tail s) (tail t) + 1)
          (lcsLen (headTail s) t))
        (lcsLen s (headTail t)) := by
  sorry

end Recurrence

/-! ## 6) (Optional) DP over `decomp` sets and correctness -/

namespace AlgorithmSketch

open BSeq

/-- Placeholder for the paper’s DP algorithm restricted to `decomp(s) × decomp(t)`.

  Later:
  * implement a DP table indexed by a finite enumeration of the decomposition sets,
  * prove it satisfies the recurrence,
  * prove it returns `lcsLen`.
-/
noncomputable def dpLen (s t : BSeq) : Nat :=
  lcsLen s t

theorem dpLen_correct (s t : BSeq) : dpLen s t = lcsLen s t := by
  rfl

end AlgorithmSketch

/-! ## 7) Future extension scaffold: annotated Dyck words (Option A)

We do *not* use this yet for the Lozano proof. This is just a placeholder for the
next phase of the project, to minimize refactoring.

The idea is:
* keep the unannotated `DyckWord` as the “shape”, so we can reuse all of Mathlib's
  decomposition and semilength machinery,
* store annotations separately, indexed by matched pairs.

When we extend to weighted/affinity matching, the recurrence changes only by replacing
`+ 1` with `+ weight` when including the first pair.
-/

namespace Extensions

structure ADyck (σ : Type) where
  shape : DyckWord
  ann   : Fin shape.semilength → σ

end Extensions

end LozanoValiente
