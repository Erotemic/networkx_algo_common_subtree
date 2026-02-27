/-
  SubtreeProofs / LozanoValiente2004.lean

  Paper-faithful core infrastructure for Lozano & Valiente (2004).

  This version fixes the build issues you reported and removes the remaining `sorry`-style gaps
  from the “forward direction” bridge:

  * Balanced sequences as `DyckWord`.
  * Context-closed one-step deletion `Del1` and containment `⊑ := ReflTransGen Del1`.
  * LCBS existence by bounded maximization over semilength.
  * Unlabeled ordered rooted trees (node labels irrelevant, edge labels ignored by encoding).
  * Edge contraction anywhere in a tree.
  * Encoding `encode : OTree β → DyckWord` (paper Def. 1 up to ignoring labels).
  * Size lemma: `semilen (encode t) = edgeCount t`.
  * Forward simulation: `Contract1 t t' → Del1 (encode t) (encode t')`.
  * Hence: `t ≼ s → encode t ⊑ encode s`.

  Still TODO (next step, still no axioms/sorries):
  * Reverse simulation: `Del1 (encode t) r → ∃ t', Contract1 t t' ∧ encode t' = r`,
    giving containment ⇒ embedding and the full MCES↔LCBS equivalence + Lemma 8 recurrence.
-/

import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace LozanoValiente

open DyckStep

abbrev BSeq : Type := DyckWord

namespace BSeq

abbrev semilen (s : BSeq) : Nat := s.semilength
abbrev head (s : BSeq) : BSeq := s.insidePart
abbrev tail (s : BSeq) : BSeq := s.outsidePart
abbrev headTail (s : BSeq) : BSeq := head s + tail s

/-! ### Paper measures on balanced sequences

The paper defines the **depth** `d(t)` and **number of leaves** `ℓ(t)` of the tree represented
by a balanced sequence `t` via the recurrences

* `d(λ) = 1`, `ℓ(λ) = 1`
* `d(0x1y) = max(d(x)+1, d(y))`, `ℓ(0x1y) = ℓ(x) + ℓ(y)`.

For `DyckWord`, `0` is the empty balanced sequence `λ`, and every nonempty word `s ≠ 0`
decomposes as `(head s).nest + tail s`.
-/

theorem semilen_eq_head_add_tail (s : BSeq) (hs : s ≠ 0) :
    semilen s = semilen (head s) + 1 + semilen (tail s) := by
  have hdecomp : (head s).nest + tail s = s := by
    simpa [head, tail] using (DyckWord.nest_insidePart_add_outsidePart (p := s) hs)
  -- take semilengths of both sides and simplify
  calc
    semilen s = semilen ((head s).nest + tail s) := by simpa [hdecomp]
    _ = semilen (head s).nest + semilen (tail s) := by
          simp [semilen]
    _ = (semilen (head s) + 1) + semilen (tail s) := by
          simp [semilen, Nat.add_assoc]
    _ = semilen (head s) + 1 + semilen (tail s) := by
          simp [Nat.add_assoc]

theorem semilen_head_lt (s : BSeq) (hs : s ≠ 0) : semilen (head s) < semilen s := by
  rw [semilen_eq_head_add_tail (s := s) hs]
  have h1 : semilen (head s) < semilen (head s) + 1 := Nat.lt_succ_self _
  have h2 : semilen (head s) + 1 ≤ semilen (head s) + 1 + semilen (tail s) :=
    Nat.le_add_right _ _
  exact lt_of_lt_of_le h1 h2

theorem semilen_tail_lt (s : BSeq) (hs : s ≠ 0) : semilen (tail s) < semilen s := by
  rw [semilen_eq_head_add_tail (s := s) hs]
  have hreorder : semilen (head s) + 1 + semilen (tail s)
      = semilen (tail s) + (semilen (head s) + 1) := by
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [hreorder, Nat.add_assoc] using
    (Nat.lt_add_of_pos_right (semilen (tail s)) (Nat.succ_pos (semilen (head s))))

noncomputable def depth : BSeq → Nat :=
  (measure semilen).wf.fix (fun s rec =>
    if hs : s = (0 : BSeq) then
      1
    else
      let hs' : s ≠ (0 : BSeq) := hs
      let dh := rec (head s) (by simpa using semilen_head_lt (s := s) hs')
      let dt := rec (tail s) (by simpa using semilen_tail_lt (s := s) hs')
      Nat.max (dh + 1) dt)

noncomputable def leafCount : BSeq → Nat :=
  (measure semilen).wf.fix (fun s rec =>
    if hs : s = (0 : BSeq) then
      1
    else
      let hs' : s ≠ (0 : BSeq) := hs
      let lh := rec (head s) (by simpa using semilen_head_lt (s := s) hs')
      let lt := rec (tail s) (by simpa using semilen_tail_lt (s := s) hs')
      lh + lt)

/-- Context-closed one-step deletion: delete exactly one matched pair, anywhere. -/
inductive Del1 : BSeq → BSeq → Prop
| core (b : BSeq) : Del1 b.nest b
| left  (a t s : BSeq) (h : Del1 t s) : Del1 (a + t) (a + s)
| right (t s c : BSeq) (h : Del1 t s) : Del1 (t + c) (s + c)
| nest  (t s : BSeq) (h : Del1 t s) : Del1 t.nest s.nest

/-- Containment: reachable by zero or more `Del1` steps. (`r ⊑ p` means from `p` delete to get `r`.) -/
def ContainedIn (r p : BSeq) : Prop := Relation.ReflTransGen Del1 p r
infix:50 " ⊑ " => ContainedIn

/-- One deletion reduces semilength by exactly 1. -/
theorem semilen_of_del1 : ∀ {t s : BSeq}, Del1 t s → semilen s + 1 = semilen t
| _, _, Del1.core b => by
    simp [semilen]
| _, _, Del1.left a t s h => by
    have ih := semilen_of_del1 (t := t) (s := s) h
    -- semilen (a+s) + 1 = semilen (a+t)
    -- both sides expand by additivity of semilength over `+`
    -- then discharge by rewriting with `ih`.
    simpa [semilen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun n => semilen a + n) ih
| _, _, Del1.right t s c h => by
    have ih := semilen_of_del1 (t := t) (s := s) h
    simpa [semilen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun n => n + semilen c) ih
| _, _, Del1.nest t s h => by
    have ih := semilen_of_del1 (t := t) (s := s) h
    -- nest adds 1 to semilength on both sides
    -- goal: semilen s.nest + 1 = semilen t.nest
    -- rewrite to: (semilen s + 1) + 1 = semilen t + 1
    have := congrArg (fun n => n + 1) ih
    simpa [semilen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

theorem semilen_le_of_del1 {t s : BSeq} (h : Del1 t s) : semilen s ≤ semilen t := by
  have eq : semilen s + 1 = semilen t := semilen_of_del1 h
  have lt : semilen s < semilen t := by
    simpa [eq] using (Nat.lt_succ_self (semilen s))
  exact Nat.le_of_lt lt

theorem semilen_le_of_containedIn {r p : BSeq} (h : r ⊑ p) : semilen r ≤ semilen p := by
  induction h with
  | refl =>
      simp [semilen]
  | tail _ hstep ih =>
      exact le_trans (semilen_le_of_del1 hstep) ih

/-- LCBS spec. -/
def IsLCBS (r p q : BSeq) : Prop :=
  r ⊑ p ∧ r ⊑ q ∧
  ∀ r', r' ⊑ p → r' ⊑ q → semilen r' ≤ semilen r

/-- Every balanced sequence can be reduced to `0`. -/
theorem zero_containedIn (p : BSeq) : (0 : BSeq) ⊑ p := by
  classical
  refine (measure semilen).wf.induction p ?_
  intro p ih
  by_cases hp : p = 0
  · subst hp
    exact Relation.ReflTransGen.refl
  ·
    -- p = head(p).nest + tail(p)
    have hdecomp : (head p).nest + tail p = p := by
      simpa [head, tail] using (DyckWord.nest_insidePart_add_outsidePart (p := p) hp)
    have hstep : Del1 p (headTail p) := by
      -- delete the outer pair around `head p` (core), lifted by right-context `tail p`
      have hcore : Del1 (head p).nest (head p) := Del1.core (head p)
      have : Del1 ((head p).nest + tail p) (head p + tail p) := Del1.right _ _ (tail p) hcore
      simpa [headTail, hdecomp, Nat.add_assoc] using this
    have hlt : semilen (headTail p) < semilen p := by
      have heq : semilen (headTail p) + 1 = semilen p := semilen_of_del1 hstep
      exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self (semilen (headTail p))) heq
    have hph : Relation.ReflTransGen Del1 p (headTail p) :=
      Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep
    have hto0 : Relation.ReflTransGen Del1 (headTail p) 0 := ih (headTail p) hlt
    exact Relation.ReflTransGen.trans hph hto0

/-- LCBS exists (bounded maximization over semilength). -/
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

noncomputable def LCBS (p q : BSeq) : BSeq := Classical.choose (exists_LCBS p q)
theorem LCBS_spec (p q : BSeq) : IsLCBS (LCBS p q) p q := by
  classical
  simpa [LCBS] using Classical.choose_spec (exists_LCBS p q)

noncomputable def lcsLen (p q : BSeq) : Nat := semilen (LCBS p q)

end BSeq

/-! ## Unlabeled ordered rooted trees + encoding -/

universe u

/-- Unlabeled rooted ordered trees with edge labels `β` (labels ignored by encoding). -/
inductive OTree (β : Type u) : Type u
| node (children : List (β × OTree β))
deriving Repr

namespace OTree

variable {β : Type u}

mutual
  def edgeCount : OTree β → Nat
  | .node cs => cs.length + edgeCountChildren cs

  def edgeCountChildren : List (β × OTree β) → Nat
  | [] => 0
  | (_, t) :: rest => edgeCount t + edgeCountChildren rest
end

/-- One-step contraction (splice a child's children into its parent's children). -/
inductive Contract1 : OTree β → OTree β → Prop
| root (before after : List (β × OTree β)) (lbl : β) (childCs : List (β × OTree β)) :
    Contract1 (.node (before ++ (lbl, .node childCs) :: after))
              (.node (before ++ childCs ++ after))
| inChild (before after : List (β × OTree β)) (lbl : β) (child child' : OTree β)
    (hrec : Contract1 child child') :
    Contract1 (.node (before ++ (lbl, child) :: after))
              (.node (before ++ (lbl, child') :: after))

/-- Embedded subtree: reflexive-transitive closure of contractions. -/
def Embeds (t s : OTree β) : Prop := Relation.ReflTransGen Contract1 s t
infix:50 " ≼ " => Embeds

namespace Encoding

open BSeq

mutual
  /-- Paper Def. 1 encoding (labels ignored): a node is encoded by the concatenation of its
      children encodings, each wrapped in a matched pair. -/
  def encode : OTree β → BSeq
  | .node cs => encodeChildren cs

  def encodeChildren : List (β × OTree β) → BSeq
  | [] => 0
  | (_, t) :: rest => (encode t).nest + encodeChildren rest
end

theorem encodeChildren_append :
    ∀ (xs ys : List (β × OTree β)),
      encodeChildren (xs ++ ys) = encodeChildren xs + encodeChildren ys
  | [], ys => by
      simp [encodeChildren]
  | (x :: xs), ys => by
      cases x with
      | mk lbl t =>
        simp [encodeChildren, encodeChildren_append xs ys]
        -- close the remaining associativity goal
        simpa [add_assoc] using
          (add_assoc (DyckWord.nest (encode t)) (encodeChildren xs) (encodeChildren ys)).symm

/-- Convenient "context factorization" of `encodeChildren` around a chosen child. -/
theorem encodeChildren_factor (before after : List (β × OTree β)) (lbl : β) (child : OTree β) :
    encodeChildren (before ++ (lbl, child) :: after)
      = encodeChildren before + (encode child).nest + encodeChildren after := by
  calc
    encodeChildren (before ++ (lbl, child) :: after)
        = encodeChildren before + encodeChildren ((lbl, child) :: after) := by
            simpa using (encodeChildren_append before ((lbl, child) :: after))
    _ = encodeChildren before + ((encode child).nest + encodeChildren after) := by
            simp [encodeChildren]
    _ = encodeChildren before + (encode child).nest + encodeChildren after := by
            simpa [add_assoc] using
              (add_assoc (encodeChildren before) ((encode child).nest) (encodeChildren after)).symm

/-- Similar factorization when the chosen child is replaced by its child-list (root contraction). -/
theorem encodeChildren_factor_splice (before after childCs : List (β × OTree β)) (lbl : β) :
    encodeChildren (before ++ (lbl, .node childCs) :: after)
      = encodeChildren before + (encodeChildren childCs).nest + encodeChildren after := by
  simpa [encode, encodeChildren] using encodeChildren_factor (β := β) before after lbl (.node childCs)

theorem encodeChildren_splice (before after childCs : List (β × OTree β)) :
    encodeChildren (before ++ childCs ++ after)
      = encodeChildren before + encodeChildren childCs + encodeChildren after := by
  calc
    encodeChildren (before ++ childCs ++ after)
        = encodeChildren before + encodeChildren (childCs ++ after) := by
            simpa [List.append_assoc] using (encodeChildren_append before (childCs ++ after))
    _ = encodeChildren before + (encodeChildren childCs + encodeChildren after) := by
            simpa using
              (congrArg (fun z => encodeChildren before + z) (encodeChildren_append childCs after))
    _ = encodeChildren before + encodeChildren childCs + encodeChildren after := by
            simpa [add_assoc] using
              (add_assoc (encodeChildren before) (encodeChildren childCs) (encodeChildren after)).symm


mutual
  theorem semilen_encode_eq_edgeCount : ∀ t : OTree β, BSeq.semilen (encode t) = OTree.edgeCount t
  | .node cs => by
      simpa [encode, OTree.edgeCount] using semilen_encodeChildren_eq_edgeCountChildren cs

  theorem semilen_encodeChildren_eq_edgeCountChildren :
      ∀ cs : List (β × OTree β),
        BSeq.semilen (encodeChildren cs) = cs.length + OTree.edgeCountChildren cs
  | [] => by
      simp [encodeChildren, OTree.edgeCountChildren, BSeq.semilen]
  | (_, t) :: rest => by
      have ht : BSeq.semilen (encode t) = OTree.edgeCount t := semilen_encode_eq_edgeCount t
      have hrest :
          BSeq.semilen (encodeChildren rest) = rest.length + OTree.edgeCountChildren rest :=
        semilen_encodeChildren_eq_edgeCountChildren rest
      simp [encodeChildren, OTree.edgeCountChildren, BSeq.semilen, ht, hrest,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
end

/-- One contraction step induces one `Del1` step on encodings. (Forward simulation.) -/
theorem contract1_implies_del1 {t t' : OTree β} (h : Contract1 t t') :
    BSeq.Del1 (encode t) (encode t') := by
  classical
  induction h with
  | root before after lbl childCs =>
      have ht : encode (.node (before ++ (lbl, .node childCs) :: after))
                = encodeChildren before + (encodeChildren childCs).nest + encodeChildren after := by
        simpa [encode] using encodeChildren_factor_splice (β := β) before after childCs lbl

      -- `hboth` gives a Del1 step between the *expressions*; we then rewrite those expressions
      -- into the exact `encode (node ...)` forms required by the goal.
      have hcore : BSeq.Del1 (encodeChildren childCs).nest (encodeChildren childCs) :=
        BSeq.Del1.core (encodeChildren childCs)

      have hleft : BSeq.Del1 (encodeChildren before + (encodeChildren childCs).nest)
                             (encodeChildren before + encodeChildren childCs) :=
        BSeq.Del1.left (encodeChildren before)
                       (encodeChildren childCs).nest
                       (encodeChildren childCs) hcore

      have hboth :
          BSeq.Del1 (encodeChildren before + (encodeChildren childCs).nest + encodeChildren after)
                    (encodeChildren before + encodeChildren childCs + encodeChildren after) :=
        BSeq.Del1.right (encodeChildren before + (encodeChildren childCs).nest)
                        (encodeChildren before + encodeChildren childCs)
                        (encodeChildren after) hleft
      -- Rewrite the *target* expression into the exact encoded contracted tree:
      have ht'' : encode (.node (before ++ (childCs ++ after)))
            = encodeChildren before + encodeChildren childCs + encodeChildren after := by
        -- expand `encode` and use append lemmas; end with associativity normalization
        calc
          encode (.node (before ++ (childCs ++ after)))
              = encodeChildren (before ++ (childCs ++ after)) := by simp [encode]
          _ = encodeChildren before + encodeChildren (childCs ++ after) := by
                simpa using (encodeChildren_append (β := β) before (childCs ++ after))
          _ = encodeChildren before + (encodeChildren childCs + encodeChildren after) := by
                simpa using congrArg (fun z => encodeChildren before + z)
                      (encodeChildren_append (β := β) childCs after)
          _ = encodeChildren before + encodeChildren childCs + encodeChildren after := by
                simpa [add_assoc] using
                  (add_assoc (encodeChildren before) (encodeChildren childCs) (encodeChildren after)).symm

      -- Turn `ht`/`ht''` into rewrite lemmas in the direction we want for `simpa`.
      have htL :
          encodeChildren before + (encodeChildren childCs).nest + encodeChildren after =
            encode (.node (before ++ (lbl, .node childCs) :: after)) := by
        simpa using ht.symm

      have htR :
          encodeChildren before + encodeChildren childCs + encodeChildren after =
            encode (.node (before ++ (childCs ++ after))) := by
        simpa using ht''.symm

      -- Now rewrite `hboth` into the exact goal shape.
      simpa [htL, htR, Nat.add_assoc] using hboth

  | inChild before after lbl child child' hrec ih =>
      -- IH: Del1 (encode child) (encode child'), lift under nest and then under concatenation contexts
      have ihn : BSeq.Del1 (encode child).nest (encode child').nest :=
        BSeq.Del1.nest (encode child) (encode child') ih
      have ht : encode (.node (before ++ (lbl, child) :: after))
                = encodeChildren before + (encode child).nest + encodeChildren after := by
        simpa [encode] using encodeChildren_factor (β := β) before after lbl child
      have ht' : encode (.node (before ++ (lbl, child') :: after))
                = encodeChildren before + (encode child').nest + encodeChildren after := by
        simpa [encode] using encodeChildren_factor (β := β) before after lbl child'
      have hleft : BSeq.Del1 (encodeChildren before + (encode child).nest)
                             (encodeChildren before + (encode child').nest) :=
        BSeq.Del1.left (encodeChildren before) (encode child).nest (encode child').nest ihn
      have hboth : BSeq.Del1 (encodeChildren before + (encode child).nest + encodeChildren after)
                             (encodeChildren before + (encode child').nest + encodeChildren after) :=
        BSeq.Del1.right (encodeChildren before + (encode child).nest)
                        (encodeChildren before + (encode child').nest)
                        (encodeChildren after) hleft
      simpa [ht, ht', Nat.add_assoc] using hboth

/-- Multi-step embedding implies multi-step containment on encodings. -/
theorem embeds_implies_contained {t s : OTree β} (h : t ≼ s) :
    BSeq.ContainedIn (encode t) (encode s) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (contract1_implies_del1 hstep)

end Encoding
end OTree

namespace PaperStatements

open BSeq

/-! ## Paper Definition 4: decomposition set D[x] -/

/-- Membership in the paper's `decomp(s)` (Definition 4). -/
inductive DecompMem (s : BSeq) : BSeq → Prop
| base : DecompMem s s
| head (t : BSeq) (ht : t ≠ 0) : DecompMem s t → DecompMem s (BSeq.head t)
| tail (t : BSeq) (ht : t ≠ 0) : DecompMem s t → DecompMem s (BSeq.tail t)
| headTail (t : BSeq) (ht : t ≠ 0) : DecompMem s t → DecompMem s (BSeq.headTail t)

/-- The paper's decomposition set `D[s] = decomp(s)`. -/
def D (s : BSeq) : Set BSeq := { t | DecompMem s t }

/-! ## Paper recurrences R[x] and S[x] (used in Lemmas 1–7, Theorem 1) -/

/-- Membership in the paper's `R[x]` set (recurrence before Lemma 2). -/
inductive RMem : BSeq → BSeq → Prop
| base : RMem (0 : BSeq) 0
| self (x : BSeq) (hx : x ≠ 0) : RMem x x
| next (x : BSeq) (hx : x ≠ 0) (z : BSeq) : RMem (BSeq.headTail x) z → RMem x z

/-- The paper's `R[x]`. -/
def R (x : BSeq) : Set BSeq := { z | RMem x z }

/-- Membership in the paper's `S[x]` set (recurrence before Lemma 2). -/
inductive SMem : BSeq → BSeq → Prop
| base : SMem (0 : BSeq) 0
| inR (x : BSeq) (hx : x ≠ 0) (z : BSeq) : RMem (BSeq.head x) z → SMem x z
| inS (x : BSeq) (hx : x ≠ 0) (z : BSeq) : SMem (BSeq.headTail x) z → SMem x z

/-- The paper's `S[x]`. -/
def S (x : BSeq) : Set BSeq := { z | SMem x z }

/-- Paper notation `R[x]{y}` = `{ z+y | z ∈ R[x] }`. -/
def RConcat (x y : BSeq) : Set BSeq := { t | ∃ z, z ∈ R x ∧ t = z + y }

/-! ## Lemmas 1–7, Corollaries 1–2, Theorem 1 -/

/-- Lemma 1: `D[y] ⊆ D[xy]`. -/
lemma Lemma1 : ∀ x y : BSeq, D y ⊆ D (x + y) := by
    sorry

/-- Lemma 2: `D[x] ⊆ D[xy] ∪ R[x]`. -/
lemma Lemma2 : ∀ x y : BSeq, D x ⊆ (D (x + y) ∪ R x) := by sorry

/-- Lemma 3: `D[0x1y] ⊆ {0x1y} ∪ D[xy] ∪ R[x]`. -/
lemma Lemma3 :
  ∀ x y : BSeq,
    D (x.nest + y) ⊆ (Set.singleton (x.nest + y) ∪ D (x + y) ∪ R x) := by sorry

/-- Lemma 4: `D[zy] ⊆ D[y] ∪ R[x]{y} ∪ S[x]` for all `z ∈ R[x]`. -/
lemma Lemma4 :
  ∀ x y z : BSeq, z ∈ R x → D (z + y) ⊆ (D y ∪ RConcat x y ∪ S x) := by sorry

/-- Corollary 1: `D[x] ⊆ R[x] ∪ S[x]`. -/
lemma Corollary1 : ∀ x : BSeq, D x ⊆ (R x ∪ S x) := by sorry

/-- Lemma 5: `S[xy] ⊆ S[x] ∪ S[y]`. -/
lemma Lemma5 : ∀ x y : BSeq, S (x + y) ⊆ (S x ∪ S y) := by sorry

/-- Lemma 6 (paper): `|S[x]| ≤ |x|·d(x) + 1`. -/
lemma Lemma6 :
  ∀ x : BSeq, Set.ncard (S x) ≤ BSeq.semilen x * depth x + 1 := by sorry

/-- Lemma 7 (paper): `|S[x]| ≤ |x|·ℓ(x) + 1`. -/
lemma Lemma7 :
  ∀ x : BSeq, Set.ncard (S x) ≤ BSeq.semilen x * leafCount x + 1 := by sorry

/-- Corollary 2 (paper): `|S[x]| ≤ |x|·min(d(x),ℓ(x)) + 1`. -/
lemma Corollary2 :
  ∀ x : BSeq, Set.ncard (S x) ≤ BSeq.semilen x * Nat.min (depth x) (leafCount x) + 1 := by sorry

/-- Theorem 1 (paper): `|D[x]| ≤ |x|·(min(d(x),ℓ(x))+1) + 1`. -/
theorem Theorem1 :
  ∀ x : BSeq,
    Set.ncard (D x) ≤ BSeq.semilen x * (Nat.min (depth x) (leafCount x) + 1) + 1 := by sorry



/-! ## Definition 5: MCES, and Theorem 2 bridge -/

namespace Trees

variable {β : Type u}

open OTree Encoding

/-- Paper Def. 5: common embedded subtree. -/
def IsCommonEmbedded (u s t : OTree β) : Prop := (u ≼ s) ∧ (u ≼ t)

/-- Paper Def. 5: maximum common embedded subtree. -/
def IsMCES (u s t : OTree β) : Prop :=
  IsCommonEmbedded (β := β) u s t ∧
  ∀ u', IsCommonEmbedded (β := β) u' s t → edgeCount u' ≤ edgeCount u

/-- Paper Theorem 2:
    LCBS of the balanced sequences of two trees is the balanced sequence of an MCES. -/
theorem Theorem2 :
  ∀ (s t : OTree β),
    ∃ u : OTree β,
      IsMCES (β := β) u s t ∧
      BSeq.IsLCBS (Encoding.encode u) (Encoding.encode s) (Encoding.encode t) := by sorry

end Trees

/-! ## Lemma 8 recurrence and Theorem 3 complexity (statements) -/

/-- Paper Lemma 8: recurrence for `lcsLen`. -/
lemma Lemma8 :
  ∀ s t : BSeq,
    BSeq.lcsLen s (0 : BSeq) = 0 ∧
    BSeq.lcsLen (0 : BSeq) t = 0 ∧
    (s ≠ 0 → t ≠ 0 →
      BSeq.lcsLen s t =
        Nat.max
          (Nat.max
            (BSeq.lcsLen (BSeq.head s) (BSeq.head t) +
             BSeq.lcsLen (BSeq.tail s) (BSeq.tail t) + 1)
            (BSeq.lcsLen (BSeq.headTail s) t))
          (BSeq.lcsLen s (BSeq.headTail t))) :=
          by sorry


/-- Paper Theorem 3 (statement): complexity bound for MCES on ordered trees. -/
theorem Theorem3 :
  ∀ {β : Type u} (s t : OTree β),
    ∃ (mcesAlg : OTree β → OTree β → OTree β)
      (steps : OTree β → OTree β → Nat),
      Trees.IsMCES (β := β) (mcesAlg s t) s t ∧
      steps s t ≤
        (OTree.edgeCount s + 1) * (OTree.edgeCount t + 1) *
        Nat.min (BSeq.depth (OTree.Encoding.encode s)) (BSeq.leafCount (OTree.Encoding.encode s)) *
        Nat.min (BSeq.depth (OTree.Encoding.encode t)) (BSeq.leafCount (OTree.Encoding.encode t)) := by
  sorry
end PaperStatements

end LozanoValiente
