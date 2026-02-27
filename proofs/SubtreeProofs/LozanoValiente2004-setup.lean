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

import Mathlib.Combinatorics.Enumerative.DyckWord

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

theorem exists_LCBS (p q : BSeq) : ∃ r : BSeq, IsLCBS r p q := by
  -- finiteness / well-foundedness argument (bounded by semilen)
  sorry

noncomputable def LCBS (p q : BSeq) : BSeq :=
  Classical.choose (exists_LCBS p q)

theorem LCBS_spec (p q : BSeq) : IsLCBS (LCBS p q) p q := by
  classical
  simpa [LCBS] using Classical.choose_spec (exists_LCBS p q)

/-- Length of LCBS in semilength units. -/
noncomputable def lcsLen (p q : BSeq) : Nat := semilen (LCBS p q)

end BSeq

/-! ## 2) Ordered rooted trees and embedded-subtree relation via edge contraction -/

/-- Rooted ordered trees with node labels `α` and edge labels `β` (children are ordered). -/
inductive OTree (α : Type u) (β : Type v) : Type (max u v)
| node (a : α) (children : List (β × OTree α β))
deriving Repr

namespace OTree

variable {α : Type u} {β : Type v}

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

theorem exists_MCES (s1 s2 : OTree α β) : ∃ t : OTree α β, IsMCES t s1 s2 := by
  -- finiteness / well-foundedness argument (bounded by edgeCount)
  sorry

noncomputable def MCES (s1 s2 : OTree α β) : OTree α β :=
  Classical.choose (exists_MCES s1 s2)

theorem MCES_spec (s1 s2 : OTree α β) : IsMCES (MCES s1 s2) s1 s2 := by
  classical
  simpa [MCES] using Classical.choose_spec (exists_MCES s1 s2)

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
    (s1 s2 : OTree α β) :
    IsLCBS (encode (MCES s1 s2)) (encode s1) (encode s2) := by
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
    (s1 s2 : OTree α β) :
    OTree.edgeCount (MCES s1 s2) = BSeq.lcsLen (encode s1) (encode s2) := by
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
