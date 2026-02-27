/-
  DRAFT formalization of:
    Lozano & Valiente (2004) "On the maximum common embedded subtree problem for ordered trees."
    https://www.cs.upc.edu/~antoni/subtree.pdf

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
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

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

/-- Paper’s `head(s)` (inside of the first matching pair). -/
abbrev head (s : BSeq) : BSeq := s.insidePart

/-- Paper’s `tail(s)` (remainder after the first matching pair). -/
abbrev tail (s : BSeq) : BSeq := s.outsidePart

/-- Paper’s `head(s) · tail(s)` (delete the outermost matched pair). -/
abbrev headTail (s : BSeq) : BSeq := s.insidePart + s.outsidePart

/-- Decomposition membership predicate (paper Definition 4). -/
inductive DecompMem : BSeq → BSeq → Prop
| base  (s : BSeq) : DecompMem s s
| head  (s t : BSeq) : DecompMem s t → DecompMem s (head t)
| tail  (s t : BSeq) : DecompMem s t → DecompMem s (tail t)
| htail (s t : BSeq) : DecompMem s t → DecompMem s (headTail t)

/-- `decompSet s` is the set `{ t | t ∈ decomp(s) }`. -/
def decompSet (s : BSeq) : Set BSeq := { t | DecompMem s t }

theorem decompSet_contains_self (s : BSeq) : s ∈ decompSet s := by
  exact DecompMem.base s

/-- Single-step deletion of a matched pair (factor form). -/
def DelAnyAnnot (t s : BSeq) : Prop :=
  ∃ a b c : BSeq,
    t = a + b.nest + c ∧
    s = a + b + c

theorem semilen_of_delAnyAnnot {t s : BSeq} (h : DelAnyAnnot t s) :
    semilen s + 1 = semilen t := by
  rcases h with ⟨a, b, c, ht, hs⟩
  subst ht
  subst hs
  simp [semilen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Containment: `r ⊑ p` means `r` is obtainable from `p` by repeated deletions. -/
def ContainedIn (r p : BSeq) : Prop :=
  Relation.ReflTransGen DelAnyAnnot p r

infix:50 " ⊑ " => ContainedIn

theorem semilen_le_of_delAnyAnnot {t s : BSeq} (h : DelAnyAnnot t s) :
    semilen s ≤ semilen t := by
  have eq : semilen s + 1 = semilen t := semilen_of_delAnyAnnot h
  have lt : semilen s < semilen t := by
    simpa [eq] using (Nat.lt_succ_self (semilen s))
  exact Nat.le_of_lt lt

theorem semilen_le_of_containedIn {r p : BSeq} (h : r ⊑ p) : semilen r ≤ semilen p := by
  induction h with
  | refl =>
      simp [semilen]
  | tail hab hstep ih =>
      exact le_trans (semilen_le_of_delAnyAnnot hstep) ih

/-- LCBS spec (Longest Common Balanced Sequence). -/
def IsLCBS (r p q : BSeq) : Prop :=
  r ⊑ p ∧ r ⊑ q ∧
  ∀ r', r' ⊑ p → r' ⊑ q → semilen r' ≤ semilen r

theorem del_headTail_of_ne_zero (p : BSeq) (hp : p ≠ 0) : DelAnyAnnot p (headTail p) := by
  refine ⟨0, head p, tail p, ?_, ?_⟩
  · simpa [head, tail] using (DyckWord.nest_insidePart_add_outsidePart (p := p) hp).symm
  · simp [headTail, head, tail]

theorem zero_containedIn (p : BSeq) : (0 : BSeq) ⊑ p := by
  classical
  refine (measure semilen).wf.induction p ?_
  intro p ih
  by_cases hp : p = 0
  · subst hp
    exact Relation.ReflTransGen.refl
  ·
    have hstep : DelAnyAnnot p (headTail p) := del_headTail_of_ne_zero p hp
    have hlt : semilen (headTail p) < semilen p := by
      have heq : semilen (headTail p) + 1 = semilen p := semilen_of_delAnyAnnot hstep
      exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self (semilen (headTail p))) heq
    have hph : Relation.ReflTransGen DelAnyAnnot p (headTail p) :=
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep
    have hto0 : Relation.ReflTransGen DelAnyAnnot (headTail p) 0 := ih (headTail p) hlt
    exact Relation.ReflTransGen.trans hph hto0

theorem exists_LCBS (p q : BSeq) : ∃ r : BSeq, IsLCBS r p q := by
  classical
  let P : Nat → Prop :=
    fun n => ∃ r : BSeq, r ⊑ p ∧ r ⊑ q ∧ semilen r = n
  have P0 : P 0 := by
    refine ⟨(0 : BSeq), zero_containedIn p, zero_containedIn q, ?_⟩
    simp [semilen]
  let bound : Nat := Nat.min (semilen p) (semilen q)
  have Pmax : P (Nat.findGreatest P bound) :=
    Nat.findGreatest_spec (m := 0) (P := P) (n := bound) (Nat.zero_le _) P0
  rcases Pmax with ⟨r, hrp, hrq, hrlen⟩
  refine ⟨r, hrp, hrq, ?_⟩
  intro r' hrp' hrq'
  have hb1 : semilen r' ≤ semilen p := semilen_le_of_containedIn hrp'
  have hb2 : semilen r' ≤ semilen q := semilen_le_of_containedIn hrq'
  have hbound : semilen r' ≤ bound := Nat.le_min_of_le_of_le hb1 hb2
  have hP : P (semilen r') := ⟨r', hrp', hrq', rfl⟩
  have hle : semilen r' ≤ Nat.findGreatest P bound :=
    Nat.le_findGreatest (m := semilen r') (P := P) (n := bound) hbound hP
  simpa [hrlen] using hle

noncomputable def LCBS (p q : BSeq) : BSeq :=
  Classical.choose (exists_LCBS p q)

theorem LCBS_spec (p q : BSeq) : IsLCBS (LCBS p q) p q := by
  classical
  simpa [LCBS] using Classical.choose_spec (exists_LCBS p q)

noncomputable def lcsLen (p q : BSeq) : Nat := semilen (LCBS p q)

end BSeq

/-! ## 2) Ordered rooted trees and embedded-subtree relation via edge contraction -/

inductive OTree (α : Type u) (β : Type v) : Type (max u v)
| node (a : α) (children : List (β × OTree α β))
deriving Repr

namespace OTree

variable {α : Type u} {β : Type v}

mutual
  def edgeCount {α : Type u} {β : Type v} : OTree α β → Nat
  | .node _ cs => cs.length + edgeCountChildren cs

  def edgeCountChildren {α : Type u} {β : Type v} :
      List (β × OTree α β) → Nat
  | [] => 0
  | (_, t) :: rest => edgeCount t + edgeCountChildren rest
end

def root : OTree α β → α
| .node a _ => a

def contractAtRoot : OTree α β → Nat → Option (OTree α β)
| .node a cs, i =>
    match cs.drop i with
    | [] => none
    | (_lbl, child) :: after =>
        match child with
        | .node _ childCs =>
            some (.node a (cs.take i ++ childCs ++ after))

inductive Contract1 : OTree α β → OTree α β → Prop
| root {t t' : OTree α β} {i : Nat} (h : contractAtRoot t i = some t') :
    Contract1 t t'
| inChild {a : α} {cs : List (β × OTree α β)} {i : Nat}
    {before after : List (β × OTree α β)}
    {lbl : β} {child child' : OTree α β}
    (hsplit : (cs.take i, cs.drop i) = (before, (lbl, child) :: after))
    (hrec   : Contract1 child child') :
    Contract1 (.node a cs) (.node a (before ++ (lbl, child') :: after))

def Embeds (t s : OTree α β) : Prop :=
  Relation.ReflTransGen Contract1 s t

infix:50 " ≼ " => Embeds

def IsCommonEmbedded (t s1 s2 : OTree α β) : Prop := (t ≼ s1) ∧ (t ≼ s2)

lemma edgeCountChildren_append (xs ys : List (β × OTree α β)) :
    edgeCountChildren (xs ++ ys) = edgeCountChildren xs + edgeCountChildren ys := by
  induction xs with
  | nil =>
      simp [edgeCountChildren]
  | cons hd tl ih =>
      cases hd with
      | mk lbl t =>
        simp [edgeCountChildren, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- One-step contraction decreases edgeCount by exactly 1. -/
theorem contract1_edgeCount {s t : OTree α β} (h : Contract1 s t) :
    edgeCount s = edgeCount t + 1 := by
  classical
  induction h with
  | root hroot =>
      rename_i s t i
      cases s with
      | node a cs =>
        -- Freeze take-prefix to avoid `length_take` / `min` pollution.
        set before : List (β × OTree α β) := cs.take i with hbefore
        have hb : cs.take i = before := hbefore.symm

        dsimp [contractAtRoot] at hroot
        cases hdrop : cs.drop i with
        | nil =>
            have : False := by
              simpa [hdrop] using hroot
            cases this
        | cons hd after =>
          cases hd with
          | mk lbl child =>
            cases child with
            | node a2 childCs =>
              have hs : some (.node a (before ++ childCs ++ after)) = some t := by
                simpa [hb, hdrop, List.append_assoc] using hroot
              have ht : t = .node a (before ++ childCs ++ after) :=
                (Option.some.inj hs).symm
              subst ht

              have hcs : cs = before ++ (lbl, .node a2 childCs) :: after := by
                have := (List.take_append_drop i cs).symm
                simpa [hb, hdrop] using this

              -- main counting
              rw [hcs]
              -- IMPORTANT: correct syntax is `simp only [...]`
              simp only [OTree.edgeCount]

              have hLenL :
                  (before ++ (lbl, .node a2 childCs) :: after).length
                    = before.length + 1 + after.length := by
                -- this is where you previously got stuck on `after.length + 1 = 1 + after.length`
                simp [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

              have hLenR :
                  (before ++ childCs ++ after).length
                    = before.length + childCs.length + after.length := by
                simp [List.length_append, List.append_assoc,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

              have hEC_L :
                  edgeCountChildren (before ++ (lbl, .node a2 childCs) :: after) =
                    edgeCountChildren before + (OTree.node a2 childCs).edgeCount + edgeCountChildren after := by
                calc
                  edgeCountChildren (before ++ (lbl, .node a2 childCs) :: after)
                      = edgeCountChildren before +
                        edgeCountChildren ((lbl, .node a2 childCs) :: after) := by
                          simpa using edgeCountChildren_append before ((lbl, .node a2 childCs) :: after)
                  _ = edgeCountChildren before +
                      ((OTree.node a2 childCs).edgeCount + edgeCountChildren after) := by
                          simp [edgeCountChildren, Nat.add_assoc]
                  _ = edgeCountChildren before + (OTree.node a2 childCs).edgeCount + edgeCountChildren after := by
                          simp [Nat.add_assoc]

              have hEC_R :
                  edgeCountChildren (before ++ childCs ++ after) =
                    edgeCountChildren before + edgeCountChildren childCs + edgeCountChildren after := by
                calc
                  edgeCountChildren (before ++ childCs ++ after)
                      = edgeCountChildren (before ++ childCs) + edgeCountChildren after := by
                          -- `before ++ childCs ++ after` parses as `before ++ (childCs ++ after)`
                          -- so use assoc once to match the append lemma
                          simpa [List.append_assoc] using
                            (edgeCountChildren_append (before ++ childCs) after)
                  _ = (edgeCountChildren before + edgeCountChildren childCs) + edgeCountChildren after := by
                          simp [edgeCountChildren_append, Nat.add_assoc]
                  _ = edgeCountChildren before + edgeCountChildren childCs + edgeCountChildren after := by
                          simp [Nat.add_assoc]

              have hChild :
                  (OTree.node a2 childCs).edgeCount = childCs.length + edgeCountChildren childCs := by
                simp only [OTree.edgeCount]

              rw [hLenL, hEC_L, hLenR, hEC_R, hChild]
              ac_rfl

  | inChild hsplit hrec ih =>
      rename_i a cs i before after lbl child child'
      have hTake : cs.take i = before := congrArg Prod.fst hsplit
      have hDrop : cs.drop i = (lbl, child) :: after := congrArg Prod.snd hsplit
      have hcs : cs = before ++ (lbl, child) :: after := by
        have := (List.take_append_drop i cs).symm
        simpa [hTake, hDrop] using this

      have ih' : edgeCount child = edgeCount child' + 1 := ih

      simp [edgeCount, edgeCountChildren, hcs,
            edgeCountChildren_append,
            List.length_append,
            ih',
            Nat.add_assoc]
      ac_rfl

theorem embeds_edgeCount_le {t s : OTree α β} (h : t ≼ s) :
    edgeCount t ≤ edgeCount s := by
  induction h with
  | refl =>
      simp
  | tail hab hstep ih =>
      rename_i b c
      have eq : edgeCount b = edgeCount c + 1 := contract1_edgeCount hstep
      have hcb : edgeCount c ≤ edgeCount b := by
        simpa [Nat.succ_eq_add_one, eq.symm] using (Nat.le_succ (edgeCount c))
      exact le_trans hcb ih

theorem leaf_embeds_of_root_eq (s0 : OTree α β) :
    (OTree.node (root s0) []) ≼ s0 := by
  classical
  refine (measure (fun t : OTree α β => edgeCount t)).wf.induction
    (C := fun s : OTree α β => (OTree.node (root s) []) ≼ s) s0 ?_
  intro s ih
  cases s with
  | node a cs =>
    cases cs with
    | nil =>
        simpa [root] using (Relation.ReflTransGen.refl : (.node a []) ≼ (.node a []))
    | cons hd rest =>
      cases hd with
      | mk lbl child =>
        cases child with
        | node a2 childCs =>
          let s' : OTree α β := .node a (childCs ++ rest)

          have hca : contractAtRoot (.node a ((lbl, .node a2 childCs) :: rest)) 0 = some s' := by
            simp [contractAtRoot, s']

          have hstep : Contract1 (.node a ((lbl, .node a2 childCs) :: rest)) s' :=
            Contract1.root hca

          have hdec : edgeCount s' < edgeCount (.node a ((lbl, .node a2 childCs) :: rest)) := by
            have eq := contract1_edgeCount hstep
            simpa [eq.symm] using (Nat.lt_succ_self (edgeCount s'))

          have hleaf : (OTree.node (root s') []) ≼ s' := ih s' hdec

          have hps : Relation.ReflTransGen Contract1 (.node a ((lbl, .node a2 childCs) :: rest)) s' :=
            Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep

          simpa [root, s'] using (Relation.ReflTransGen.trans hps hleaf)

/-- Maximum common embedded subtree (MCES), by edge-count maximality. -/
def IsMCES (t s1 s2 : OTree α β) : Prop :=
  IsCommonEmbedded t s1 s2 ∧
  ∀ t', IsCommonEmbedded t' s1 s2 → edgeCount t' ≤ edgeCount t

theorem exists_MCES (s1 s2 : OTree α β) (hroot : root s1 = root s2) :
    ∃ t : OTree α β, IsMCES t s1 s2 := by
  classical
  let N := Nat.min (edgeCount s1) (edgeCount s2)

  let P : Nat → Prop :=
    fun n => ∃ t : OTree α β, IsCommonEmbedded t s1 s2 ∧ edgeCount t = n

  have P0 : P 0 := by
    refine ⟨OTree.node (root s1) [], ?_, by simp [edgeCount, edgeCountChildren]⟩
    constructor
    · exact leaf_embeds_of_root_eq s1
    · have : root s2 = root s1 := by simpa [hroot] using rfl
      simpa [this] using (leaf_embeds_of_root_eq s2)

  have Pbnd : ∀ n, P n → n ≤ N := by
    intro n hn
    rcases hn with ⟨t, ⟨h1, h2⟩, rfl⟩
    have hn1 : edgeCount t ≤ edgeCount s1 := embeds_edgeCount_le h1
    have hn2 : edgeCount t ≤ edgeCount s2 := embeds_edgeCount_le h2
    exact Nat.le_min_of_le_of_le hn1 hn2

  let nmax := Nat.findGreatest P N
  have hnmaxP : P nmax := by
    have h : P (Nat.findGreatest P N) :=
      Nat.findGreatest_spec (P := P) (n := N) (m := 0) (Nat.zero_le N) P0
    simpa [nmax] using h

  rcases hnmaxP with ⟨t, htCommon, htEq⟩
  refine ⟨t, ?_⟩
  refine ⟨htCommon, ?_⟩
  intro t' ht'Common
  have ht' : P (edgeCount t') := ⟨t', ht'Common, rfl⟩
  have leN : edgeCount t' ≤ N := Pbnd _ ht'
  have : edgeCount t' ≤ nmax := Nat.le_findGreatest leN ht'
  simpa [nmax, htEq] using this

noncomputable def MCES (s1 s2 : OTree α β) (h : root s1 = root s2) : OTree α β :=
  Classical.choose (exists_MCES (s1 := s1) (s2 := s2) h)

theorem MCES_spec (s1 s2 : OTree α β) (h : root s1 = root s2) :
    IsMCES (MCES s1 s2 h) s1 s2 := by
  classical
  simpa [MCES] using Classical.choose_spec (exists_MCES (s1 := s1) (s2 := s2) h)

end OTree

/-! ## 3) Encoding trees as balanced sequences (paper Definition 1) -/

namespace Encoding

open BSeq
open OTree

variable {α : Type u} {β : Type v}

mutual
  def encode : OTree α β → BSeq
  | .node _ cs => encodeChildren cs

  def encodeChildren : List (β × OTree α β) → BSeq
  | [] => 0
  | (_, t) :: rest => (encode t).nest + encodeChildren rest
end

mutual
  theorem semilen_encode_eq_edgeCount :
      ∀ t : OTree α β, BSeq.semilen (encode t) = OTree.edgeCount t
  | .node _ cs => by
      simpa [encode, OTree.edgeCount] using
        (semilen_encodeChildren_eq_edgeCountChildren cs)

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
end

theorem contract1_implies_delAnyAnnot
    {t t' : OTree α β} (h : OTree.Contract1 t t') :
    BSeq.DelAnyAnnot (encode t) (encode t') := by
  sorry

theorem embeds_implies_contained
    {t s : OTree α β} (h : t ≼ s) :
    (encode t) ⊑ (encode s) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hab hstep ih =>
      exact Relation.ReflTransGen.tail ih (contract1_implies_delAnyAnnot hstep)

theorem contained_implies_exists_embedded_with_encoding
    {s : OTree α β} {r : BSeq} (h : r ⊑ (encode s)) :
    ∃ t : OTree α β, t ≼ s ∧ encode t = r := by
  sorry

end Encoding

namespace Recurrence

open BSeq

theorem lcsLen_empty_left (t : BSeq) :
    lcsLen 0 t = 0 := by
  classical
  have hspec := (LCBS_spec (p := (0 : BSeq)) (q := t))
  have hcont : (LCBS (0 : BSeq) t) ⊑ (0 : BSeq) := hspec.1
  have hle : semilen (LCBS (0 : BSeq) t) ≤ semilen (0 : BSeq) :=
    semilen_le_of_containedIn hcont
  have hzero : semilen (LCBS (0 : BSeq) t) = 0 := by
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

namespace AlgorithmSketch

open BSeq

noncomputable def dpLen (s t : BSeq) : Nat :=
  lcsLen s t

theorem dpLen_correct (s t : BSeq) : dpLen s t = lcsLen s t := by
  rfl

end AlgorithmSketch

namespace Extensions

structure ADyck (σ : Type) where
  shape : DyckWord
  ann   : Fin shape.semilength → σ

end Extensions



/-!
## Paper statements: Facts/Lemmas/Corollaries/Theorems (Lozano–Valiente 2004)

This section collects *named statements* corresponding to the numbered results in the paper.
Most proofs are left as `sorry` for now; the goal is to keep the development aligned with the paper
and to make it easy to fill proofs incrementally.

These statements are intended to live in the *full* development file, not the tree-only v2 scratch.
-/
namespace Paper

open BSeq
open OTree

/-- Paper `D[x]` (Definition 4) is our decomposition set. -/
abbrev D (x : BSeq) : Set BSeq := BSeq.decompSet x

/-
The paper defines depth `d(x)` and leaf-count `ℓ(x)` via recurrences (Section 2).
We will replace these stubs with well-founded definitions later.
-/
noncomputable def depth (_x : BSeq) : Nat := 0
noncomputable def leaves (_x : BSeq) : Nat := 0

/-! ### Auxiliary sets `R[x]` and `S[x]` (paper Section 2) -/

/-- Membership in paper’s `R[x]`. -/
inductive RMem : BSeq → BSeq → Prop
| base : RMem 0 0
| self {x : BSeq} (hx : x ≠ 0) : RMem x x
| step {x z : BSeq} (hx : x ≠ 0) : RMem (BSeq.headTail x) z → RMem x z

/-- Membership in paper’s `S[x]`. -/
inductive SMem : BSeq → BSeq → Prop
| base : SMem 0 0
| ofR {x z : BSeq} (hx : x ≠ 0) : RMem (BSeq.head x) z → SMem x z
| ofS {x z : BSeq} (hx : x ≠ 0) : SMem (BSeq.headTail x) z → SMem x z

def Rset (x : BSeq) : Set BSeq := { z | RMem x z }
def Sset (x : BSeq) : Set BSeq := { z | SMem x z }

/-- Paper notation `R[x]{y}` (concatenate elements of `R[x]` with a fixed suffix `y`). -/
def Rconcat (x y : BSeq) : Set BSeq := { w | ∃ z, RMem x z ∧ w = z + y }

theorem DecompMem.lift {s t u : BSeq} (hst : BSeq.DecompMem s t) :
    BSeq.DecompMem t u → BSeq.DecompMem s u := by
  intro htu
  induction htu with
  | base =>
      simpa using hst
  | head _ _ ih =>
      exact BSeq.DecompMem.head _ _ ih
  | tail _ _ ih =>
      exact BSeq.DecompMem.tail _ _ ih
  | htail _ _ ih =>
      exact BSeq.DecompMem.htail _ _ ih

theorem decompSet_subset_of_mem {s t : BSeq} (ht : t ∈ BSeq.decompSet s) :
    BSeq.decompSet t ⊆ BSeq.decompSet s := by
  intro u hu
  -- unfold membership
  dsimp [BSeq.decompSet] at ht hu ⊢
  exact (DecompMem.lift ht) hu

/-- Key auxiliary fact needed for Lemma 2:
decomposing any `R`-element stays within `D(x+y) ∪ Rset x`. -/
theorem decomp_of_R_subset (x y z : BSeq) (hz : RMem x z) :
    D z ⊆ (D (x + y) ∪ Rset x) := by
  -- proof is by induction on `hz : RMem x z`
  -- base: x=z=0, trivial
  -- self: z=x, then use Lemma1-ish closure into D(x+y) and/or keep in Rset
  -- step: hz : RMem (headTail x) z, use IH and then lift `RMem (headTail x)` to `RMem x` via `RMem.step`
  sorry

theorem tail_add_of_ne_empty (x y : BSeq) (hx : x ≠ BSeq.empty) :
    BSeq.tail (x + y) = BSeq.tail x + y := by
  -- decompose x = (head x).nest + tail x
  have hxdecomp : (BSeq.head x).nest + BSeq.tail x = x := by
    simpa [BSeq.head, BSeq.tail] using
      (DyckWord.nest_insidePart_add_outsidePart (p := x) hx)
  -- now reassociate x+y into (head x).nest + (tail x + y)
  calc
    BSeq.tail (x + y)
        = BSeq.tail (((BSeq.head x).nest + BSeq.tail x) + y) := by simpa [hxdecomp]
    _ = BSeq.tail ((BSeq.head x).nest + (BSeq.tail x + y)) := by
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc]
    _ = BSeq.tail x + y := by
          -- `tail (a.nest + b) = b`
          simp [BSeq.tail, BSeq.head]


/-! ### Numbered results (statements) -/


/-- Definition 3 (paper): for nonempty `s`, `s = 0 head(s) 1 tail(s)`.
In DyckWord form: `head(s).nest + tail(s) = s`. -/
theorem def3_headTail_decomp (s : BSeq) (hs : s ≠ 0) :
    (BSeq.head s).nest + (BSeq.tail s) = s := by
  simpa [BSeq.head, BSeq.tail] using
    DyckWord.nest_insidePart_add_outsidePart (p := s) hs

/-- Lemma 1 (paper): `D[y] ⊆ D[xy]`. -/
theorem lemma1 (x y : BSeq) : D y ⊆ D (x + y) := by
  classical
  /- Helper: compose a derivation `s ⟶* t` with `t ⟶* u` to get `s ⟶* u`. -/
  have lift : ∀ {s t u : BSeq}, BSeq.DecompMem s t → BSeq.DecompMem t u → BSeq.DecompMem s u := by
    intro s t u hst htu
    induction htu with
    | base =>
        simpa using hst
    | head _ _ ih =>
        exact BSeq.DecompMem.head _ _ ih
    | tail _ _ ih =>
        exact BSeq.DecompMem.tail _ _ ih
    | htail _ _ ih =>
        exact BSeq.DecompMem.htail _ _ ih

  /- Helper: if `t ∈ D s` then `D t ⊆ D s`. -/
  have decomp_subset_of_mem : ∀ {s t : BSeq}, t ∈ BSeq.decompSet s → BSeq.decompSet t ⊆ BSeq.decompSet s := by
    intro s t ht u hu
    dsimp [BSeq.decompSet] at ht hu ⊢
    exact lift ht hu

  /- Helper: semilen(tail x) < semilen x for nonempty x. -/
  have semilen_tail_lt : ∀ {x : BSeq}, x ≠ BSeq.empty → BSeq.semilen (BSeq.tail x) < BSeq.semilen x := by
    intro x hx
    -- decompose x = (head x).nest + tail x
    have hdecomp : (BSeq.head x).nest + BSeq.tail x = x := by
      simpa [BSeq.head, BSeq.tail] using
        (DyckWord.nest_insidePart_add_outsidePart (p := x) hx)
    -- take semilengths
    have hlen :
        BSeq.semilen x = BSeq.semilen (BSeq.head x) + 1 + BSeq.semilen (BSeq.tail x) := by
      -- `simp` knows semilength of `+` and `.nest`
      -- (this is exactly what you used in `semilen_of_delAnyAnnot`)
      calc
        BSeq.semilen x = BSeq.semilen ((BSeq.head x).nest + BSeq.tail x) := by simpa [hdecomp]
        _ = BSeq.semilen (BSeq.head x).nest + BSeq.semilen (BSeq.tail x) := by
              simp [BSeq.semilen]
        _ = (BSeq.semilen (BSeq.head x) + 1) + BSeq.semilen (BSeq.tail x) := by
              simp [BSeq.semilen, Nat.add_assoc]
        _ = BSeq.semilen (BSeq.head x) + 1 + BSeq.semilen (BSeq.tail x) := by
              simp [Nat.add_assoc]
    -- now show tail < head+1+tail
    -- rewrite RHS as tail + (head+1) and use lt_add_of_pos_right
    have : BSeq.semilen (BSeq.tail x) <
        BSeq.semilen (BSeq.tail x) + (BSeq.semilen (BSeq.head x) + 1) := by
      exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
    -- commute/associate into the shape in `hlen`
    -- and finish
    simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

  /- Helper: tail (x+y) = tail x + y for x≠empty. -/
  have tail_add_of_ne_empty : ∀ (x y : BSeq), x ≠ BSeq.empty → BSeq.tail (x + y) = BSeq.tail x + y := by
    intro x y hx
    have hdecomp : (BSeq.head x).nest + BSeq.tail x = x := by
      simpa [BSeq.head, BSeq.tail] using
        (DyckWord.nest_insidePart_add_outsidePart (p := x) hx)
    calc
      BSeq.tail (x + y)
          = BSeq.tail (((BSeq.head x).nest + BSeq.tail x) + y) := by simpa [hdecomp]
      _ = BSeq.tail ((BSeq.head x).nest + (BSeq.tail x + y)) := by
            simp [add_assoc]
      _ = BSeq.tail x + y := by
            -- outsidePart of `a.nest + b` is `b`
            simp [BSeq.tail, BSeq.head]

  /- Step 1: show `y ∈ D(x+y)` by WF induction on semilen(x). -/
  have hy_mem : y ∈ D (x + y) := by
    -- Prove `P x := y ∈ D (x+y)`
    let P : BSeq → Prop := fun x => y ∈ D (x + y)
    refine (measure BSeq.semilen).wf.induction (C := P) x ?_
    intro x ih
    by_cases hx : x = BSeq.empty
    · subst hx
      -- y ∈ D (empty + y) = D y
      -- base case of decomposition
      -- (unfold D if necessary)
      simpa [BSeq.empty, add_assoc, BSeq.decompSet] using (BSeq.DecompMem.base y)
    ·
      -- tail(x+y) is in D(x+y)
      have htail_mem : BSeq.tail (x + y) ∈ D (x + y) := by
        -- `tail` is a one-step DecompMem from self
        -- (unfold D if necessary)
        dsimp [D, BSeq.decompSet]
        exact BSeq.DecompMem.tail _ _ (BSeq.DecompMem.base _)
      -- closure: D(tail(x+y)) ⊆ D(x+y)
      have hsub : D (BSeq.tail (x + y)) ⊆ D (x + y) := by
        -- unfold and use decomp_subset_of_mem
        -- (convert D to decompSet if D is an abbrev)
        simpa [D] using (decomp_subset_of_mem (s := x + y) (t := BSeq.tail (x + y)) (by simpa [D] using htail_mem))
      -- apply IH to tail x (strictly smaller)
      have hlt : BSeq.semilen (BSeq.tail x) < BSeq.semilen x := semilen_tail_lt (x := x) (by simpa [BSeq.empty] using hx)
      have ih_tail : y ∈ D (BSeq.tail x + y) := ih (BSeq.tail x) hlt
      have : y ∈ D (BSeq.tail (x + y)) := by
        simpa [tail_add_of_ne_empty x y (by simpa [BSeq.empty] using hx)] using ih_tail
      exact hsub this

  /- Step 2: if y ∈ D(x+y), then D(y) ⊆ D(x+y) by closure. -/
  -- unfold D to decompSet and apply the closure lemma
  -- (this `simpa [D]` handles the case where `D` is just an abbrev)
  simpa [D] using (decomp_subset_of_mem (s := x + y) (t := y) (by simpa [D] using hy_mem))


/-- Lemma 2 (paper): `D[x] ⊆ D[xy] ∪ R[x]`. -/
theorem lemma2 (x y : BSeq) : D x ⊆ (D (x + y) ∪ Rset x) := by
  classical
  -- We follow the paper's induction on `|x|` (here: `semilen x`).
  let P : BSeq → Prop := fun x => D x ⊆ (D (x + y) ∪ Rset x)
  refine (measure BSeq.semilen).wf.induction (C := P) x ?_
  intro x ih t ht
  -- unfold set membership
  dsimp [P, D, BSeq.decompSet] at ht ⊢

  -- helper: for empty start word, all decompositions are empty
  have decomp_from_empty_eq_empty : ∀ {t : BSeq}, BSeq.DecompMem 0 t → t = 0 := by
    intro t ht
    induction ht with
    | base => rfl
    | head _ _ ih => simpa [BSeq.head, ih]
    | tail _ _ ih => simpa [BSeq.tail, ih]
    | htail _ _ ih =>
        -- `headTail 0 = 0`
        simpa [BSeq.headTail, BSeq.head, BSeq.tail, ih]

  by_cases hx0 : x = 0
  · subst hx0
    have ht0 : t = 0 := decomp_from_empty_eq_empty ht
    subst ht0
    exact Or.inr (by
      dsimp [Rset]
      exact RMem.base)

  -- local helpers about `head` / `headTail` under concatenation
  have head_add_of_ne_empty (x y : BSeq) (hx : x ≠ 0) : BSeq.head (x + y) = BSeq.head x := by
    have hxdecomp : (BSeq.head x).nest + BSeq.tail x = x := def3_headTail_decomp x hx
    calc
      BSeq.head (x + y) = BSeq.head (((BSeq.head x).nest + BSeq.tail x) + y) := by simpa [hxdecomp]
      _ = BSeq.head ((BSeq.head x).nest + (BSeq.tail x + y)) := by simp [add_assoc]
      _ = BSeq.head x := by
            -- `head (a.nest + b) = a`
            simp [BSeq.head, BSeq.tail]

  have headTail_add_of_ne_empty (x y : BSeq) (hx : x ≠ 0) :
      BSeq.headTail (x + y) = BSeq.headTail x + y := by
    -- headTail = head + tail
    simp [BSeq.headTail, head_add_of_ne_empty x y hx, tail_add_of_ne_empty x y hx, add_assoc]

  have semilen_headTail_lt (x : BSeq) (hx : x ≠ 0) : BSeq.semilen (BSeq.headTail x) < BSeq.semilen x := by
    have hxdecomp : (BSeq.head x).nest + BSeq.tail x = x := def3_headTail_decomp x hx
    have hlen :
        BSeq.semilen x = BSeq.semilen (BSeq.head x) + 1 + BSeq.semilen (BSeq.tail x) := by
      calc
        BSeq.semilen x = BSeq.semilen ((BSeq.head x).nest + BSeq.tail x) := by simpa [hxdecomp]
        _ = BSeq.semilen (BSeq.head x).nest + BSeq.semilen (BSeq.tail x) := by
              simp [BSeq.semilen]
        _ = (BSeq.semilen (BSeq.head x) + 1) + BSeq.semilen (BSeq.tail x) := by
              simp [BSeq.semilen, Nat.add_assoc]
        _ = BSeq.semilen (BSeq.head x) + 1 + BSeq.semilen (BSeq.tail x) := by
              simp [Nat.add_assoc]
    have hhtlen :
        BSeq.semilen (BSeq.headTail x) = BSeq.semilen (BSeq.head x) + BSeq.semilen (BSeq.tail x) := by
      simp [BSeq.headTail, BSeq.semilen, BSeq.head, BSeq.tail]
    -- now: a+b < a+1+b
    have : BSeq.semilen (BSeq.head x) + BSeq.semilen (BSeq.tail x) <
        BSeq.semilen (BSeq.head x) + BSeq.semilen (BSeq.tail x) + 1 :=
      Nat.lt_succ_self _
    -- rewrite target using computed lengths
    simpa [hhtlen, hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

  -- classification: any `t ∈ D x` is either `t = x` or lies in one of the immediate sub-decompositions
  have decomp_cases :
      (t = x) ∨ BSeq.DecompMem (BSeq.head x) t ∨ BSeq.DecompMem (BSeq.tail x) t ∨ BSeq.DecompMem (BSeq.headTail x) t := by
    induction ht with
    | base =>
        exact Or.inl rfl
    | head s u ih =>
        rcases ih with rfl | h
        · exact Or.inr (Or.inl (BSeq.DecompMem.base (BSeq.head s)))
        · rcases h with h | h
          · exact Or.inr (Or.inl (BSeq.DecompMem.head _ _ h))
          · rcases h with h | h
            · exact Or.inr (Or.inr (Or.inl (BSeq.DecompMem.head _ _ h)))
            · exact Or.inr (Or.inr (Or.inr (BSeq.DecompMem.head _ _ h)))
    | tail s u ih =>
        rcases ih with rfl | h
        · exact Or.inr (Or.inr (Or.inl (BSeq.DecompMem.base (BSeq.tail s))))
        · rcases h with h | h
          · exact Or.inr (Or.inl (BSeq.DecompMem.tail _ _ h))
          · rcases h with h | h
            · exact Or.inr (Or.inr (Or.inl (BSeq.DecompMem.tail _ _ h)))
            · exact Or.inr (Or.inr (Or.inr (BSeq.DecompMem.tail _ _ h)))
    | htail s u ih =>
        rcases ih with rfl | h
        · exact Or.inr (Or.inr (Or.inr (BSeq.DecompMem.base (BSeq.headTail s))))
        · rcases h with h | h
          · exact Or.inr (Or.inl (BSeq.DecompMem.htail _ _ h))
          · rcases h with h | h
            · exact Or.inr (Or.inr (Or.inl (BSeq.DecompMem.htail _ _ h)))
            · exact Or.inr (Or.inr (Or.inr (BSeq.DecompMem.htail _ _ h)))

  -- case split using the classification
  rcases decomp_cases with rfl | h
  · exact Or.inr (by dsimp [Rset]; exact RMem.self hx0)
  · rcases h with hHead | h
    · -- D(head x) ⊆ D(x+y)
      have hhead_mem : BSeq.head x ∈ BSeq.decompSet (x + y) := by
        have : BSeq.DecompMem (x + y) (BSeq.head (x + y)) :=
          BSeq.DecompMem.head _ _ (BSeq.DecompMem.base _)
        simpa [BSeq.decompSet, head_add_of_ne_empty x y hx0] using this
      have hsub : BSeq.decompSet (BSeq.head x) ⊆ BSeq.decompSet (x + y) :=
        decompSet_subset_of_mem (s := x + y) (t := BSeq.head x) hhead_mem
      exact Or.inl (hsub hHead)
    · rcases h with hTail | hHT
      · -- D(tail x) ⊆ D(headTail x) by Lemma 1
        have hIntoHT : t ∈ BSeq.decompSet (BSeq.headTail x) := by
          have hsub : D (BSeq.tail x) ⊆ D (BSeq.head x + BSeq.tail x) :=
            lemma1 (BSeq.head x) (BSeq.tail x)
          simpa [D, BSeq.headTail] using (hsub hTail)
        -- now headTail case
        have hlt : BSeq.semilen (BSeq.headTail x) < BSeq.semilen x := semilen_headTail_lt x hx0
        have ih' := ih (BSeq.headTail x) hlt
        have ht' : t ∈ D (BSeq.headTail x) := by
          simpa [D, BSeq.decompSet] using hIntoHT
        have hres : t ∈ (D (BSeq.headTail x + y) ∪ Rset (BSeq.headTail x)) := ih' ht'
        cases hres with
        | inl hDy =>
            have hht_mem : BSeq.headTail (x + y) ∈ BSeq.decompSet (x + y) := by
              dsimp [BSeq.decompSet]
              exact BSeq.DecompMem.htail _ _ (BSeq.DecompMem.base _)
            have hsub' : BSeq.decompSet (BSeq.headTail (x + y)) ⊆ BSeq.decompSet (x + y) :=
              decompSet_subset_of_mem (s := x + y) (t := BSeq.headTail (x + y)) hht_mem
            have : t ∈ D (BSeq.headTail (x + y)) := by
              simpa [headTail_add_of_ne_empty x y hx0, add_assoc] using hDy
            exact Or.inl (by simpa [D] using hsub' (by simpa [D] using this))
        | inr hR =>
            exact Or.inr (by dsimp [Rset] at hR ⊢; exact RMem.step hx0 hR)
      · -- headTail-case directly
        have hlt : BSeq.semilen (BSeq.headTail x) < BSeq.semilen x := semilen_headTail_lt x hx0
        have ih' := ih (BSeq.headTail x) hlt
        have ht' : t ∈ D (BSeq.headTail x) := by
          simpa [D, BSeq.decompSet] using hHT
        have hres : t ∈ (D (BSeq.headTail x + y) ∪ Rset (BSeq.headTail x)) := ih' ht'
        cases hres with
        | inl hDy =>
            have hht_mem : BSeq.headTail (x + y) ∈ BSeq.decompSet (x + y) := by
              dsimp [BSeq.decompSet]
              exact BSeq.DecompMem.htail _ _ (BSeq.DecompMem.base _)
            have hsub' : BSeq.decompSet (BSeq.headTail (x + y)) ⊆ BSeq.decompSet (x + y) :=
              decompSet_subset_of_mem (s := x + y) (t := BSeq.headTail (x + y)) hht_mem
            have : t ∈ D (BSeq.headTail (x + y)) := by
              simpa [headTail_add_of_ne_empty x y hx0, add_assoc] using hDy
            exact Or.inl (by simpa [D] using hsub' (by simpa [D] using this))
        | inr hR =>
            exact Or.inr (by dsimp [Rset] at hR ⊢; exact RMem.step hx0 hR)


/-- Lemma 3 (paper): `D[0x1y] ⊆ {0x1y} ∪ D[xy] ∪ R[x]`.
In DyckWord: `0x1y` is `x.nest + y`. -/
theorem lemma3 (x y : BSeq) :
    D (x.nest + y) ⊆ ({x.nest + y} ∪ D (x + y) ∪ Rset x) := by
  classical
  intro t ht
  -- unfold D
  dsimp [D, BSeq.decompSet] at ht ⊢

  let s0 : BSeq := x.nest + y
  have ht' : BSeq.DecompMem s0 t := by
    simpa [s0] using ht
  clear ht

  -- helper: compose DecompMem derivations
  have lift :
      ∀ {s a b : BSeq}, BSeq.DecompMem s a → BSeq.DecompMem a b → BSeq.DecompMem s b := by
    intro s a b hsa hab
    induction hab with
    | base  => simpa using hsa
    | head _ _ ih => exact BSeq.DecompMem.head _ _ ih
    | tail _ _ ih => exact BSeq.DecompMem.tail _ _ ih
    | htail _ _ ih => exact BSeq.DecompMem.htail _ _ ih

  -- if u ∈ D s then D u ⊆ D s
  have decomp_subset_of_mem :
      ∀ {s u : BSeq}, BSeq.DecompMem s u → (D u ⊆ D s) := by
    intro s u hsu w huw
    dsimp [D, BSeq.decompSet] at huw ⊢
    exact lift hsu huw

  -- RMem implies membership in D (since R is built by repeated headTail)
  have RMem_to_Decomp : ∀ {x u : BSeq}, RMem x u → BSeq.DecompMem x u := by
    intro x u hu
    induction hu with
    | base =>
        exact BSeq.DecompMem.base 0
    | self hx =>
        (expose_names; exact DecompMem.base x_2)
    | step hx _ ih =>
        -- headTail x ∈ D x
        have hxht : BSeq.DecompMem x (BSeq.headTail x) :=
          BSeq.DecompMem.htail _ _ (BSeq.DecompMem.base x)
        -- and u ∈ D(headTail x) by IH
        expose_names
        sorry
        --exact lift hxht ih

  -- handy facts about s0
  have hhead0 : BSeq.head s0 = x := by
    simp [s0, BSeq.head]
  have htail0 : BSeq.tail s0 = y := by
    simp [s0, BSeq.tail]
  have hht0 : BSeq.headTail s0 = x + y := by
    simp [BSeq.headTail, s0, BSeq.head, BSeq.tail]

  -- x ∈ Rset x (handles both x=0 and x≠0)
  have hxR : x ∈ Rset x := by
    dsimp [Rset]
    by_cases hx : x = 0
    · subst hx; exact RMem.base
    · exact RMem.self hx

  -- y ∈ D(x+y) via Lemma 1 since y ∈ D y
  have hyDxy : y ∈ D (x + y) := by
    have hyDy : y ∈ D y := by
      dsimp [D, BSeq.decompSet]
      exact BSeq.DecompMem.base y
    exact (lemma1 x y) hyDy

  -- (x+y) ∈ D(x+y)
  have hxyDxy : (x + y) ∈ D (x + y) := by
    dsimp [D, BSeq.decompSet]
    exact BSeq.DecompMem.base (x + y)

  -- Main induction over decomposition derivation
  induction ht' with
  | base  =>
      -- t = s0
      exact Or.inl (Or.inl (by simp [s0]))
  | head u _ ih =>
      -- t = head u
      cases ih with
      | inl h_left =>
          cases h_left with
          | inl hu0 =>
              -- u = s0 -> head u = x ∈ Rset x
              subst hu0
              exact Or.inr (by simpa [hhead0] using hxR)
          | inr huD =>
              -- u ∈ D(x+y) -> head u ∈ D(x+y)
              exact Or.inl (Or.inr (BSeq.DecompMem.head _ _ huD))
      | inr huR =>
          -- u ∈ Rset x -> u ∈ D x -> head u ∈ D x -> lemma2 gives head u ∈ D(x+y) ∪ Rset x
          have huDx : u ∈ D x := by
            dsimp [D, BSeq.decompSet]
            exact RMem_to_Decomp huR
          have hsub : D u ⊆ D x := decomp_subset_of_mem (s := x) (u := u) (by
            dsimp [D, BSeq.decompSet] at huDx; exact huDx)
          have hheadDu : BSeq.head u ∈ D u := by
            dsimp [D, BSeq.decompSet]
            exact BSeq.DecompMem.head _ _ (BSeq.DecompMem.base u)
          have hheadDx : BSeq.head u ∈ D x := hsub hheadDu
          have h2 : (BSeq.head u ∈ D (x + y) ∪ Rset x) := (lemma2 x y) hheadDx
          cases h2 with
          | inl hD => exact Or.inl (Or.inr hD)
          | inr hR => exact Or.inr hR
  | tail u _ ih =>
      -- t = tail u
      cases ih with
      | inl h_left =>
          cases h_left with
          | inl hu0 =>
              -- u = s0 -> tail u = y ∈ D(x+y)
              subst hu0
              exact Or.inl (Or.inr (by simpa [htail0] using hyDxy))
          | inr huD =>
              exact Or.inl (Or.inr (BSeq.DecompMem.tail _ _ huD))
      | inr huR =>
          have huDx : u ∈ D x := by
            dsimp [D, BSeq.decompSet]
            exact RMem_to_Decomp huR
          have hsub : D u ⊆ D x := decomp_subset_of_mem (s := x) (u := u) (by
            dsimp [D, BSeq.decompSet] at huDx; exact huDx)
          have htailDu : BSeq.tail u ∈ D u := by
            dsimp [D, BSeq.decompSet]
            exact BSeq.DecompMem.tail _ _ (BSeq.DecompMem.base u)
          have htailDx : BSeq.tail u ∈ D x := hsub htailDu
          have h2 : (BSeq.tail u ∈ D (x + y) ∪ Rset x) := (lemma2 x y) htailDx
          cases h2 with
          | inl hD => exact Or.inl (Or.inr hD)
          | inr hR => exact Or.inr hR
  | htail u _ ih =>
      -- t = headTail u
      cases ih with
      | inl h_left =>
          cases h_left with
          | inl hu0 =>
              -- u = s0 -> headTail u = x+y ∈ D(x+y)
              subst hu0
              exact Or.inl (Or.inr (by sorry))
          | inr huD =>
              exact Or.inl (Or.inr (BSeq.DecompMem.htail _ _ huD))
      | inr huR =>
          have huDx : u ∈ D x := by
            dsimp [D, BSeq.decompSet]
            exact RMem_to_Decomp huR
          have hsub : D u ⊆ D x := decomp_subset_of_mem (s := x) (u := u) (by
            dsimp [D, BSeq.decompSet] at huDx; exact huDx)
          have hhtDu : BSeq.headTail u ∈ D u := by
            dsimp [D, BSeq.decompSet]
            exact BSeq.DecompMem.htail _ _ (BSeq.DecompMem.base u)
          have hhtDx : BSeq.headTail u ∈ D x := hsub hhtDu
          have h2 : (BSeq.headTail u ∈ D (x + y) ∪ Rset x) := (lemma2 x y) hhtDx
          cases h2 with
          | inl hD => exact Or.inl (Or.inr hD)
          | inr hR => exact Or.inr hR

/-- Lemma 4 (paper): `D[zy] ⊆ D[y] ∪ R[x]{y} ∪ S[x]` for all `z ∈ R[x]`. -/
lemma lemma4 (x y z : BSeq) (hz : RMem x z) :
    D (z + y) ⊆ (D y ∪ Rconcat x y ∪ Sset x) := by
  classical

  -- We follow the paper: induction on `|z|` (here: `semilen z`).
  -- We prove a slightly more general statement that quantifies `x`.
  let P : BSeq → Prop := fun z =>
    ∀ x : BSeq, RMem x z → D (z + y) ⊆ (D y ∪ Rconcat x y ∪ Sset x)

  -- Helper: `semilen (headTail z) < semilen z` for nonempty `z`.
  have semilen_headTail_lt : ∀ {z : BSeq}, z ≠ 0 → BSeq.semilen (BSeq.headTail z) < BSeq.semilen z := by
    intro z hz0
    have hdecomp : (BSeq.head z).nest + (BSeq.tail z) = z := def3_headTail_decomp z hz0
    have hlen :
        BSeq.semilen z = BSeq.semilen (BSeq.head z) + 1 + BSeq.semilen (BSeq.tail z) := by
      calc
        BSeq.semilen z = BSeq.semilen ((BSeq.head z).nest + BSeq.tail z) := by
          simpa [hdecomp]
        _ = BSeq.semilen (BSeq.head z).nest + BSeq.semilen (BSeq.tail z) := by
          simp [BSeq.semilen]
        _ = (BSeq.semilen (BSeq.head z) + 1) + BSeq.semilen (BSeq.tail z) := by
          simp [BSeq.semilen, Nat.add_assoc]
        _ = BSeq.semilen (BSeq.head z) + 1 + BSeq.semilen (BSeq.tail z) := by
          simp [Nat.add_assoc]
    have hhtlen :
        BSeq.semilen (BSeq.headTail z) = BSeq.semilen (BSeq.head z) + BSeq.semilen (BSeq.tail z) := by
      simp [BSeq.headTail, BSeq.semilen, BSeq.head, BSeq.tail]
    -- a+b < a+1+b
    have :
        BSeq.semilen (BSeq.head z) + BSeq.semilen (BSeq.tail z) <
          BSeq.semilen (BSeq.head z) + BSeq.semilen (BSeq.tail z) + 1 :=
      Nat.lt_succ_self _
    simpa [hhtlen, hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

  -- Helper: `RMem x z` implies `RMem x (headTail z)`.
  have RMem_headTail_closed : ∀ {x z : BSeq}, RMem x z → RMem x (BSeq.headTail z) := by
    intro x z hz
    induction hz
    case base =>
      simpa [BSeq.headTail, BSeq.head, BSeq.tail] using (RMem.base : RMem 0 0)

    case self x' hx =>
      -- goal: RMem x' (headTail x')
      by_cases hht : BSeq.headTail x' = 0
      · have this : RMem (BSeq.headTail x') (BSeq.headTail x') := by
          simpa [hht] using (RMem.base : RMem 0 0)
        exact RMem.step hx this
      · have this : RMem (BSeq.headTail x') (BSeq.headTail x') :=
          RMem.self (by simpa using hht)
        exact RMem.step hx this

    case step x' z' hx hz ih =>
      -- ih : RMem (headTail x') (headTail z')
      exact RMem.step hx ih

  -- Helper: `Sset` is monotone along `RMem` (structural induction on `RMem`).
  have Sset_mono_of_RMem : ∀ {x z : BSeq}, RMem x z → Sset z ⊆ Sset x := by
    intro x z hz
    intro w hw
    dsimp [Sset] at hw ⊢
    induction hz with
    | base =>
        simpa using hw
    | self _ =>
        simpa using hw
    | step hx hz ih =>
        rename_i x' z'
        exact SMem.ofS hx (ih hw)

  -- Main induction.
  have hmain : P z := by
    refine (measure BSeq.semilen).wf.induction (C := P) z ?_
    intro z ih
    intro x hz
    intro w hw
    by_cases hz0 : z = 0
    · subst hz0
      -- D(0+y)=D(y)
      have : w ∈ D y := by
        simpa [D, BSeq.decompSet] using hw
      -- put it into the leftmost union branch
      have : w ∈ D y ∪ (Rconcat x y ∪ Sset x) := Or.inl this
      simpa [Set.union_assoc] using this
    ·
      -- Rewrite `z+y` into the `0x1y` form so we can apply Lemma 3.
      have hz_decomp : (BSeq.head z).nest + BSeq.tail z = z := def3_headTail_decomp z hz0
      have hz_add : z + y = (BSeq.head z).nest + (BSeq.tail z + y) := by
        calc
          z + y = ((BSeq.head z).nest + BSeq.tail z) + y := by simpa [hz_decomp]
          _ = (BSeq.head z).nest + (BSeq.tail z + y) := by simp [add_assoc]
      have hlem3 := lemma3 (BSeq.head z) (BSeq.tail z + y)
      have hw' : w ∈ ({z + y} ∪ (D (BSeq.headTail z + y) ∪ Rset (BSeq.head z))) := by
        -- apply Lemma 3 after rewriting
        have hw0 : w ∈ ({(BSeq.head z).nest + (BSeq.tail z + y)} ∪ D ((BSeq.head z) + (BSeq.tail z + y)) ∪ Rset (BSeq.head z)) :=
          hlem3 (by simpa [hz_add] using hw)
        -- normalize unions and the middle `D` term
        -- (head z + (tail z + y)) = (headTail z) + y
        have : w ∈ ({z + y} ∪ (D (BSeq.headTail z + y) ∪ Rset (BSeq.head z))) := by
          -- reassociate unions
          -- and rewrite the singleton and D-term
          sorry
        exact this
      -- split the three cases
      cases hw' with
      | inl hw_singleton =>
          -- {z+y} ⊆ Rconcat x y using `hz : RMem x z`
          have : w ∈ Rconcat x y := by
            rcases hw_singleton with rfl
            refine ⟨z, hz, rfl⟩
          have : w ∈ D y ∪ (Rconcat x y ∪ Sset x) := Or.inr (Or.inl this)
          simpa [Set.union_assoc] using this
      | inr hw_rest =>
          cases hw_rest with
          | inl hw_Dht =>
              -- IH on headTail z
              have hz_ht : RMem x (BSeq.headTail z) := RMem_headTail_closed hz
              have hlt : BSeq.semilen (BSeq.headTail z) < BSeq.semilen z := semilen_headTail_lt (z := z) hz0
              have ih' : P (BSeq.headTail z) := ih (BSeq.headTail z) hlt
              have hsub : D (BSeq.headTail z + y) ⊆ (D y ∪ Rconcat x y ∪ Sset x) := ih' x hz_ht
              exact hsub hw_Dht
          | inr hw_Rhead =>
              -- R[head z] ⊆ S[x]
              have : w ∈ Sset x := by
                -- first put `w` into `Sset z` via `ofR`, then lift along `hz : RMem x z`.
                have hwSz : w ∈ Sset z := by
                  dsimp [Sset]
                  exact SMem.ofR hz0 hw_Rhead
                have hwSx : w ∈ Sset x := Sset_mono_of_RMem hz hwSz
                exact hwSx
              have : w ∈ D y ∪ (Rconcat x y ∪ Sset x) := Or.inr (Or.inr this)
              simpa [Set.union_assoc] using this

  -- apply the general result to the specific `x,z`.
  exact hmain x hz


/-- Corollary 1 (paper): `D[x] ⊆ R[x] ∪ S[x]`. -/
theorem corollary1 (x : BSeq) : D x ⊆ (Rset x ∪ Sset x) := by
  sorry

/-- Lemma 5 (paper): `S[xy] ⊆ S[x] ∪ S[y]`. -/
theorem Lemma5 : ∀ x y : BSeq, Sset (x + y) ⊆ (Sset x ∪ Sset y) := by
  classical

  -- semilen = 0 -> word = 0
  have eq_zero_of_semilen_eq_zero : ∀ {p : BSeq}, BSeq.semilen p = 0 → p = 0 := by
    intro p hp
    have hlen : (↑p : List DyckStep).length = 0 := by
      have h : (↑p : List DyckStep).length = 2 * p.semilength := by
        simpa using (DyckWord.two_mul_semilength_eq_length (p := p)).symm
      simpa [hp] using h
    have hnil : (↑p : List DyckStep) = [] := (List.length_eq_zero_iff).1 hlen
    simpa using (DyckWord.toList_eq_nil (p := p)).1 hnil

  intro x
  -- Induction on semilen(x), proving: ∀ y, Sset(x+y) ⊆ Sset x ∪ Sset y
  refine (measure BSeq.semilen).wf.induction
    (C := fun x => ∀ y : BSeq, Sset (x + y) ⊆ (Sset x ∪ Sset y)) x ?_
  intro x ih y z hz

  -- `hz : z ∈ Sset (x+y)` is definitionaly `SMem (x+y) z`
  have hzmem : SMem (x + y) z := hz

  by_cases hx : x = 0
  · subst hx
    exact Or.inr hz
  ·
    -- Generalize x+y to avoid dependent-elim headaches
    generalize hsxy : x + y = sxy at hzmem

    cases hzmem with
    | base =>
        -- In this branch: sxy = 0 and z = 0, so hsxy becomes x+y=0
        have hxy0 : x + y = 0 := by
          simpa using hsxy
        -- semilen(x+y)=0 -> semilen x = 0 -> x=0, contradict hx
        have hsem0 : BSeq.semilen (x + y) = 0 := by
          simpa [hxy0] using (rfl : BSeq.semilen (0 : BSeq) = 0)
        have hsum0 : BSeq.semilen x + BSeq.semilen y = 0 := by
          simpa [BSeq.semilen, DyckWord.semilength_add] using hsem0
        have hx0 : BSeq.semilen x = 0 := (Nat.add_eq_zero_iff.mp hsum0).1
        have : x = 0 := eq_zero_of_semilen_eq_zero hx0
        exact (hx this).elim

    | ofR hsxy_ne0 hr =>
        -- hr : RMem (head sxy) z; rewrite sxy = x+y, then head(x+y)=head x (since x≠0)
        have hr1 : RMem (BSeq.head (x + y)) z := by
          -- use hsxy to rewrite
          simpa [hsxy] using hr
        have hr' : RMem (BSeq.head x) z := by
          simpa [BSeq.head,
                DyckWord.insidePart_add (p := x) (q := y) hx] using hr1
        exact Or.inl (SMem.ofR hx hr')

    | ofS hsxy_ne0 hs =>
        -- hs : SMem (headTail sxy) z; rewrite to headTail(x+y) then to headTail x + y
        have hs1 : SMem (BSeq.headTail (x + y)) z := by
          simpa [hsxy] using hs
        have hs' : SMem (BSeq.headTail x + y) z := by
          simpa [BSeq.headTail, BSeq.head, BSeq.tail, add_assoc,
                DyckWord.insidePart_add (p := x) (q := y) hx,
                DyckWord.outsidePart_add (p := x) (q := y) hx] using hs1

        -- semilen(headTail x) < semilen x
        have hlt : BSeq.semilen (BSeq.headTail x) < BSeq.semilen x := by
          have hxdecomp :
              BSeq.semilen (BSeq.head x) + BSeq.semilen (BSeq.tail x) + 1 = BSeq.semilen x := by
            simpa [BSeq.semilen, BSeq.head, BSeq.tail, Nat.add_assoc] using
              (DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one (p := x) hx)
          have hht :
              BSeq.semilen (BSeq.headTail x)
                = BSeq.semilen (BSeq.head x) + BSeq.semilen (BSeq.tail x) := by
            simpa [BSeq.headTail, BSeq.semilen] using
              (DyckWord.semilength_add (p := BSeq.head x) (q := BSeq.tail x))
          have : BSeq.semilen (BSeq.headTail x) + 1 = BSeq.semilen x := by
            simpa [hht, Nat.add_assoc] using hxdecomp
          exact lt_of_lt_of_eq (Nat.lt_succ_self _) this

        have ih' := ih (BSeq.headTail x) hlt y
        -- IMPORTANT: apply subset with explicit implicit binder
        have hzU : z ∈ (Sset (BSeq.headTail x) ∪ Sset y) := (ih' (a := z) hs')
        rcases hzU with hzL | hzR
        · exact Or.inl (SMem.ofS hx hzL)
        · exact Or.inr hzR

/-- Fact 2 (paper): `|R[x]| = |x| + 1`. -/
theorem fact2 (x : BSeq) [Fintype {z // RMem x z}] :
    Fintype.card {z // RMem x z} = BSeq.semilen x + 1 := by
  sorry

/-- Lemma 6 (paper): `|S[x]| ≤ |x| d(x) + 1`. -/
theorem lemma6 (x : BSeq) [Fintype {z // SMem x z}] :
    Fintype.card {z // SMem x z} ≤ BSeq.semilen x * depth x + 1 := by
  sorry

/-- Lemma 7 (paper): `|S[x]| ≤ |x| ℓ(x) + 1`. -/
theorem lemma7 (x : BSeq) [Fintype {z // SMem x z}] :
    Fintype.card {z // SMem x z} ≤ BSeq.semilen x * leaves x + 1 := by
  sorry

/-- Corollary 2 (paper): `|S[x]| ≤ |x| min(d(x),ℓ(x)) + 1`. -/
theorem corollary2 (x : BSeq) [Fintype {z // SMem x z}] :
    Fintype.card {z // SMem x z} ≤
      BSeq.semilen x * Nat.min (depth x) (leaves x) + 1 := by
  sorry

/-- Theorem 1 (paper): `|D[x]| ≤ |x|(min(d(x),ℓ(x)) + 1) + 1`. -/
theorem theorem1 (x : BSeq) [Fintype {z // BSeq.DecompMem x z}] :
    Fintype.card {z // BSeq.DecompMem x z} ≤
      BSeq.semilen x * (Nat.min (depth x) (leaves x) + 1) + 1 := by
  sorry

-- Lemma 8 is already stated as `Recurrence.lemma8_recurrence` in the main development.

-- Theorem 2 is stated/proved via `Encoding` + `MainTheorem` parts of the development.

/- Paper Theorem 3 (statement): complexity bound for MCES on ordered trees. -/
theorem Theorem3 :
  ∀ {α : Type u} {β : Type v}
    (s t : OTree α β) (hroot : OTree.root s = OTree.root t),
    ∃ (mcesAlg : OTree α β → OTree α β → OTree α β)
      (steps : OTree α β → OTree α β → Nat),
      OTree.IsMCES (mcesAlg s t) s t ∧
      steps s t ≤
        (OTree.edgeCount s + 1) * (OTree.edgeCount t + 1) *
        Nat.min (Paper.depth (Encoding.encode s)) (Paper.leaves (Encoding.encode s)) *
        Nat.min (Paper.depth (Encoding.encode t)) (Paper.leaves (Encoding.encode t)) := by
  intro α β s t hroot
  sorry

end Paper


end LozanoValiente
