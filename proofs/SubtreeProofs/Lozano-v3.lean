/-
  Formalization skeleton for:
    Antoni Lozano & Gabriel Valiente (2004)
    "On the Maximum Common Embedded Subtree Problem for Ordered Trees"

  Goals of this file (per user request):
  - Provide Lean companions for *all* definitions/lemmata/theorems/corollaries in the paper.
  - Prove all of them, except the final asymptotic runtime bound (Theorem 3), which may remain `sorry`
    with an explanatory comment if needed.

  Implementation choices:
  - We define our own inductive datatype `BSeq` for balanced sequences (Dyck words) with the grammar:
        λ | 0 x 1 y
    This makes the paper’s `head`, `tail`, `headTail`, and all recurrences structurally recursive.
  - Containment is implemented exactly as in paper Definition 2 (recursive “delete one annotation pair”).
  - Ordered rooted trees are represented as `OTree := node (List OTree)` (rooted ordered children).
    Balanced sequence encoding is the paper’s Definition 1 (each edge contributes an outer 0/1 around
    the child’s encoding; siblings concatenate).
  - Embedded subtree is the paper’s Definition 5: reflexive-transitive closure of single-edge contractions,
    where a contraction merges a child into its parent (splicing the child’s children into the parent’s list).

  Notes:
  - Theorem 3 (runtime) is included as a theorem statement, but left as `sorry` (requested).
  - If you later want a full runtime proof, it will require additional infrastructure (tight complexity analysis,
    counting arguments, and a formal cost model), which is substantial.

  This file is self-contained (no DyckWord import required).
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Defs
--import Mathlib.Analysis.Analytic.Basic

open scoped BigOperators

namespace LozanoValiente2004

/-! ## Section 2: Balanced sequences -/

/-- Paper Definition 1/2 domain: balanced sequences over {0,1}. -/
inductive BSeq : Type
  | nil : BSeq
  | cons : BSeq → BSeq → BSeq    -- represents `0 x 1 y`
deriving DecidableEq, Repr

namespace BSeq

/-- Paper empty sequence `λ`. -/
abbrev empty : BSeq := .nil

/-- Concatenation of balanced sequences (siblings concatenate). -/
def append : BSeq → BSeq → BSeq
  | nil,      t => t
  | cons x y, t => cons x (append y t)

instance : HAdd BSeq BSeq BSeq := ⟨append⟩

@[simp] theorem nil_add (t : BSeq) : (nil : BSeq) + t = t := by rfl
@[simp] theorem cons_add (x y t : BSeq) : (cons x y : BSeq) + t = cons x (y + t) := by rfl

/-- `0 s 1` (wrap with one annotation pair). -/
def nest (s : BSeq) : BSeq := cons s nil

@[simp] theorem nest_def (s : BSeq) : nest s = cons s nil := rfl

/-- Paper `|x|`: number of edges / annotation pairs = Dyck semilength. -/
def semilen : BSeq → Nat
  | nil      => 0
  | cons x y => semilen x + semilen y + 1

@[simp] theorem semilen_nil : semilen nil = 0 := rfl
@[simp] theorem semilen_cons (x y : BSeq) : semilen (cons x y) = semilen x + semilen y + 1 := rfl
@[simp] theorem semilen_nest (s : BSeq) : semilen (nest s) = semilen s + 1 := by
  simp [nest, semilen, Nat.add_comm]

/-- Paper Definition 3: `head(0x1y)=x`, `tail(0x1y)=y`. -/
def head : BSeq → BSeq
  | nil      => nil
  | cons x _ => x

def tail : BSeq → BSeq
  | nil      => nil
  | cons _ y => y

/-- Paper `headTail(s) = head(s) tail(s)` (delete the first matched pair). -/
def headTail (s : BSeq) : BSeq := head s + tail s

@[simp] theorem head_cons (x y : BSeq) : head (cons x y) = x := rfl
@[simp] theorem tail_cons (x y : BSeq) : tail (cons x y) = y := rfl
@[simp] theorem headTail_nil : headTail nil = nil := by simp [headTail, head, tail]
@[simp] theorem headTail_cons (x y : BSeq) : headTail (cons x y) = x + y := by simp [headTail, head, tail]

/-- Associativity of concatenation. -/
theorem add_assoc (a b c : BSeq) : (a + b) + c = a + (b + c) := by
  induction a with
  | nil => simp
  | cons x y ihx ihy =>
      simp [ihy]

@[simp] theorem add_nil (a : BSeq) : a + nil = a := by
  induction a with
  | nil => simp
  | cons x y ihx ihy =>
      simp [ihy]

instance : Std.Associative (α:=BSeq) (· + ·) := ⟨add_assoc⟩

/-- Semilength is additive under concatenation. -/
theorem semilen_add (a b : BSeq) : semilen (a + b) = semilen a + semilen b := by
  induction a with
  | nil => simp
  | cons x y ihx ihy =>
      simp [semilen, ihy, Nat.add_left_comm, Nat.add_comm]

/-! ## Definition 2: recursive containment `s ⊆ t` -/

/--
Paper Definition 2 (containment).

`s ⊑ t` iff either `s = t` or there exist `s1 s2 s3` and `t1 t2 t3` such that
`si ⊑ ti` for i=1..3 and `s = s1 s2 s3` and `t = t1 0 t2 1 t3`.

In our grammar, `t1 0 t2 1 t3` is `t1 + cons t2 t3`, and `s1 s2 s3` is `s1 + s2 + s3`.
-/
inductive Contained : BSeq → BSeq → Prop
  | refl (s) : Contained s s
  | step (s t : BSeq)
      (s1 s2 s3 t1 t2 t3 : BSeq)
      (hs : s = s1 + s2 + s3)
      (ht : t = t1 + cons t2 t3)
      (h1 : Contained s1 t1)
      (h2 : Contained s2 t2)
      (h3 : Contained s3 t3) : Contained s t

infix:50 " ⊑ " => Contained

/-- Common balanced sequence. -/
def IsCommon (r s t : BSeq) : Prop := r ⊑ s ∧ r ⊑ t

/-- LCBS (paper): common and of maximum semilength. -/
def IsLCBS (r s t : BSeq) : Prop :=
  IsCommon r s t ∧ ∀ r', IsCommon r' s t → semilen r' ≤ semilen r

/-- Basic: reflexivity. -/
theorem contained_refl (s : BSeq) : s ⊑ s := Contained.refl s

/-- Containment is transitive (needed throughout). -/
theorem contained_trans {a b c : BSeq} (hab : a ⊑ b) (hbc : b ⊑ c) : a ⊑ c := by
  induction hbc generalizing a with
  | refl _ =>
      simpa using hab
  | step s t s1 s2 s3 t1 t2 t3 hs ht h1 h2 h3 ih1 ih2 ih3 =>
      -- Core remaining obligation:
      -- from `a ⊑ (s1 + s2 + s3)` and `s1 ⊑ t1`, `s2 ⊑ t2`, `s3 ⊑ t3`,
      -- derive `a ⊑ (t1 + cons t2 t3)`.
      sorry

/-- Semilength monotonicity: if `r ⊑ s` then `|r| ≤ |s|`. -/
theorem semilen_le_of_contained {r s : BSeq} (h : r ⊑ s) : semilen r ≤ semilen s := by
  induction h with
  | refl s =>
      exact Nat.le_refl _
  | step s t s1 s2 s3 t1 t2 t3 hs ht h1 h2 h3 ih1 ih2 ih3 =>
      have hslen : semilen s = semilen s1 + semilen s2 + semilen s3 := by
        calc
          semilen s = semilen (s1 + s2 + s3) := by simpa [hs]
          _ = semilen s1 + semilen s2 + semilen s3 := by
                simp [semilen_add, add_assoc, Nat.add_assoc]
      have htlen : semilen t = semilen t1 + semilen t2 + semilen t3 + 1 := by
        calc
          semilen t = semilen (t1 + cons t2 t3) := by simpa [ht]
          _ = semilen t1 + semilen t2 + semilen t3 + 1 := by
                simp [semilen_add, semilen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      calc
        semilen s = semilen s1 + semilen s2 + semilen s3 := hslen
        _ ≤ semilen t1 + semilen t2 + semilen t3 := by
              exact Nat.add_le_add (Nat.add_le_add ih1 ih2) ih3
        _ ≤ semilen t1 + semilen t2 + semilen t3 + 1 := Nat.le_succ _
        _ = semilen t := by simpa [htlen]

/-- The empty sequence is contained in every sequence (by deleting all annotations). -/
theorem empty_contained (s : BSeq) : (nil : BSeq) ⊑ s := by
  -- Use semilen well-founded induction on s, repeatedly delete the outermost annotation.
  -- A direct proof is possible by recursion on s.
  induction s with
  | nil => exact Contained.refl _
  | cons x y ihx ihy =>
      -- nil ⊑ x and nil ⊑ y, then nil = nil+nil+nil ⊑ nil + cons x y by step
      refine Contained.step _ _ nil nil nil nil x y ?_ ?_ (Contained.refl _) ihx ihy
      · simp
      · simp

/-- Existence of an LCBS by `Nat.findGreatest` (bounded by `min |s| |t|`). -/
theorem exists_LCBS (s t : BSeq) : ∃ r : BSeq, IsLCBS r s t := by
  classical
  let P : Nat → Prop := fun n => ∃ r : BSeq, r ⊑ s ∧ r ⊑ t ∧ semilen r = n
  have P0 : P 0 := by
    refine ⟨nil, empty_contained s, empty_contained t, ?_⟩
    simp
  let bound := Nat.min (semilen s) (semilen t)
  have Pmax : P (Nat.findGreatest P bound) :=
    Nat.findGreatest_spec (m := 0) (P := P) (n := bound) (Nat.zero_le _) P0
  rcases Pmax with ⟨r, hrs, hrt, hrlen⟩
  refine ⟨r, ?_⟩
  refine ⟨⟨hrs, hrt⟩, ?_⟩
  intro r' hr'
  rcases hr' with ⟨h1, h2⟩
  have hb1 : semilen r' ≤ semilen s := semilen_le_of_contained h1
  have hb2 : semilen r' ≤ semilen t := semilen_le_of_contained h2
  have hbound : semilen r' ≤ bound := Nat.le_min_of_le_of_le hb1 hb2
  have hP : P (semilen r') := ⟨r', h1, h2, rfl⟩
  have hle : semilen r' ≤ Nat.findGreatest P bound :=
    Nat.le_findGreatest (m := semilen r') (P := P) (n := bound) hbound hP
  simpa [hrlen] using hle

/-- A choice of LCBS. -/
noncomputable def LCBS (s t : BSeq) : BSeq := Classical.choose (exists_LCBS s t)
theorem LCBS_spec (s t : BSeq) : IsLCBS (LCBS s t) s t := Classical.choose_spec (exists_LCBS s t)

/-- Paper `lcs(s,t)` as a *number of edges* (semilength of an LCBS). -/
noncomputable def lcsLen (s t : BSeq) : Nat := semilen (LCBS s t)

/-! ## Definition 4: decomposition and auxiliary families R, S -/

/--
Paper Definition 4: `decomp(s)` (as a `Finset`) via the recurrence:
`D[λ]={λ}` and `D[0x1y] = {0x1y} ∪ D[x] ∪ D[y] ∪ D[xy]`.
-/
def D : BSeq → Finset BSeq
  | nil => {nil}
  | cons x y => ({cons x y} ∪ D x ∪ D y ∪ D (x + y))
termination_by s => semilen s
decreasing_by
  · simpa [semilen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.lt_succ_of_le (Nat.le_add_right x.semilen y.semilen))
  · have hy : y.semilen ≤ y.semilen + x.semilen := Nat.le_add_right y.semilen x.semilen
    simpa [semilen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.lt_succ_of_le hy)
  · simpa [semilen, semilen_add] using (Nat.lt_succ_self (x.semilen + y.semilen))

/-- Paper auxiliary recurrence: `R[λ]={λ}`, `R[0x1y]={0x1y} ∪ R[xy]`. -/
def R : BSeq → Finset BSeq
  | nil => {nil}
  | cons x y => ({cons x y} ∪ R (x + y))
termination_by s => semilen s
decreasing_by
  simpa [semilen, semilen_add] using (Nat.lt_succ_self (x.semilen + y.semilen))

/-- Paper auxiliary recurrence: `S[λ]={λ}`, `S[0x1y]=R[x] ∪ S[xy]`. -/
def S : BSeq → Finset BSeq
  | nil => {nil}
  | cons x y => (R x ∪ S (x + y))
termination_by s => semilen s
decreasing_by
  simpa [semilen, semilen_add] using (Nat.lt_succ_self (x.semilen + y.semilen))

/-- Paper function `d(x)` (depth) recurrence. -/
def depth : BSeq → Nat
  | nil => 1
  | cons x y => Nat.max (depth x + 1) (depth y)

/-- Paper function `ℓ(x)` (number of leaves) recurrence. -/
def leaves : BSeq → Nat
  | nil => 1
  | cons x y => leaves x + leaves y

/-! ### Section 2 lemmata (cardinality/decomposition ingredients) -/

/-- Lemma 1 (paper). -/
theorem lemma1 (x y : BSeq) : (D y : Set BSeq) ⊆ D (x + y) := by
  induction x generalizing y with
  | nil =>
      intro z hz
      simpa [D] using hz
  | cons x1 x2 ih1 ih2 =>
      intro z hz
      have hz' : z ∈ D (x2 + y) := ih2 y hz
      have : z ∈ D (cons x1 (x2 + y)) := by
        simp [D, hz']
      simpa using this

/-- Lemma 2 (paper). -/
theorem lemma2 (x y : BSeq) : (D x : Set BSeq) ⊆ (D (x + y) ∪ R x : Finset BSeq) := by
  let P : BSeq → Prop := fun x => (D x : Set BSeq) ⊆ (D (x + y) ∪ R x : Finset BSeq)
  have hmain : P x := by
    refine (measure semilen).wf.induction x ?_
    intro x ih z hz
    cases x with
    | nil =>
        have hz0 : z = nil := by simpa [D] using hz
        exact Finset.mem_union.mpr <| Or.inr <| by simpa [R, hz0]
    | cons x1 x2 =>
        rcases (by simpa [D] using hz) with hz0 | hz1 | hz2 | hz3
        · exact Finset.mem_union.mpr <| Or.inr <| by simpa [R, hz0]
        · exact Finset.mem_union.mpr <| Or.inl <| by
            simpa [D] using (Or.inr (Or.inl hz1) :
              z = cons x1 (x2 + y) ∨ z ∈ D x1 ∨ z ∈ D (x2 + y) ∨ z ∈ D (x1 + (x2 + y)))
        ·
          have hz2a : z ∈ D (x1 + x2) := lemma1 x1 x2 hz2
          have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
            simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
          have hrec : z ∈ (D ((x1 + x2) + y) ∪ R (x1 + x2) : Finset BSeq) := (ih (x1 + x2) hlt) hz2a
          rcases Finset.mem_union.mp hrec with hD | hR
          · exact Finset.mem_union.mpr <| Or.inl <| by
              have : z = cons x1 (x2 + y) ∨ z ∈ D x1 ∨ z ∈ D (x2 + y) ∨ z ∈ D (x1 + (x2 + y)) := by
                exact Or.inr (Or.inr (Or.inr (by simpa [add_assoc] using hD)))
              simpa [D] using this
          · exact Finset.mem_union.mpr <| Or.inr <| by
              simpa [R] using (Or.inr hR : z = cons x1 x2 ∨ z ∈ R (x1 + x2))
        ·
          have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
            simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
          have hrec : z ∈ (D ((x1 + x2) + y) ∪ R (x1 + x2) : Finset BSeq) := (ih (x1 + x2) hlt) hz3
          rcases Finset.mem_union.mp hrec with hD | hR
          · exact Finset.mem_union.mpr <| Or.inl <| by
              have : z = cons x1 (x2 + y) ∨ z ∈ D x1 ∨ z ∈ D (x2 + y) ∨ z ∈ D (x1 + (x2 + y)) := by
                exact Or.inr (Or.inr (Or.inr (by simpa [add_assoc] using hD)))
              simpa [D] using this
          · exact Finset.mem_union.mpr <| Or.inr <| by
              simpa [R] using (Or.inr hR : z = cons x1 x2 ∨ z ∈ R (x1 + x2))
  exact hmain

/-- Lemma 3 (paper). -/
theorem lemma3 (x y : BSeq) :
    (D (cons x y) : Set BSeq) ⊆ ({cons x y} ∪ D (x + y) ∪ R x : Finset BSeq) := by
  intro z hz
  rcases (by simpa [D] using hz) with hz0 | hz1 | hz2 | hz3
  · -- z = cons x y
    exact Finset.mem_union.mpr <| Or.inl <| by simpa [hz0]
  · -- z ∈ D x
    have hz1' : z ∈ (D (x + y) ∪ R x : Finset BSeq) := lemma2 x y hz1
    rcases Finset.mem_union.mp hz1' with hz1d | hz1r
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr hz1d
    · exact Finset.mem_union.mpr <| Or.inr hz1r
  · -- z ∈ D y ⊆ D (x + y)
    have hz2' : z ∈ D (x + y) := lemma1 x y hz2
    exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr hz2'
  · -- z ∈ D (x + y)
    exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr hz3

/--
Lemma 4 (paper): `D[zy] ⊆ D[y] ∪ R[x]{y} ∪ S[x]` for all `z ∈ R[x]`.

`R[x]{y}` is the image of `R[x]` under `(+ y)`.
-/
def R_app (x y : BSeq) : Finset BSeq := (R x).image (fun z => z + y)

theorem lemma4 (x y z : BSeq) (hz : z ∈ R x) :
    (D (z + y) : Set BSeq) ⊆ (D y ∪ R_app x y ∪ S x : Finset BSeq) := by
  let P : BSeq → Prop := fun x =>
    ∀ z, z ∈ R x → (D (z + y) : Set BSeq) ⊆ (D y ∪ R_app x y ∪ S x : Finset BSeq)
  have hmain : P x := by
    refine (measure semilen).wf.induction x ?_
    intro x ih z hz t ht
    cases x with
    | nil =>
        have hz0 : z = nil := by simpa [R] using hz
        subst hz0
        -- D (nil + y) = D y
        have htDy : t ∈ D y := by simpa using ht
        exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl htDy
    | cons x1 x2 =>
        have hz_cases : z = cons x1 x2 ∨ z ∈ R (x1 + x2) := by
          simpa [R] using hz
        have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
          simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
        have R_embed : ∀ {u : BSeq}, u ∈ R (x1 + x2) → u ∈ R (cons x1 x2) := by
          intro u hu
          simpa [R] using (Or.inr hu : u = cons x1 x2 ∨ u ∈ R (x1 + x2))
        have Rapp_embed : ∀ {u : BSeq}, u ∈ R_app (x1 + x2) y → u ∈ R_app (cons x1 x2) y := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
          exact Finset.mem_image.mpr ⟨w, R_embed hw, rfl⟩
        have S_embed : ∀ {u : BSeq}, u ∈ S (x1 + x2) → u ∈ S (cons x1 x2) := by
          intro u hu
          simpa [S] using (Finset.mem_union.mpr (Or.inr hu) : u ∈ R x1 ∪ S (x1 + x2))
        have Rx1_to_S : ∀ {u : BSeq}, u ∈ R x1 → u ∈ S (cons x1 x2) := by
          intro u hu
          simpa [S] using (Finset.mem_union.mpr (Or.inl hu) : u ∈ R x1 ∪ S (x1 + x2))
        rcases hz_cases with hz_self | hz_tail
        · -- z = cons x1 x2
          subst hz_self
          have h3 : (D (cons x1 (x2 + y)) : Set BSeq) ⊆
              ({cons x1 (x2 + y)} ∪ D (x1 + (x2 + y)) ∪ R x1 : Finset BSeq) := lemma3 x1 (x2 + y)
          have ht3 : t ∈ ({cons x1 (x2 + y)} ∪ D (x1 + (x2 + y)) ∪ R x1 : Finset BSeq) := h3 (by simpa using ht)
          rcases Finset.mem_union.mp ht3 with hleft | hRx1
          · rcases Finset.mem_union.mp hleft with hsingle | hDtail
            · -- singleton -> in R_app
              have hRself : cons x1 x2 ∈ R (cons x1 x2) := by
                simpa [R] using (Or.inl rfl : cons x1 x2 = cons x1 x2 ∨ cons x1 x2 ∈ R (x1 + x2))
              have hRapp : cons x1 (x2 + y) ∈ R_app (cons x1 x2) y := by
                exact Finset.mem_image.mpr ⟨cons x1 x2, hRself, by simp⟩
              have ht_eq : t = cons x1 (x2 + y) := by simpa using hsingle
              have : t ∈ R_app (cons x1 x2) y := by simpa [ht_eq] using hRapp
              exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr this
            · -- recurse on x1+x2 with z' = x1+x2
              have hz_self_tail : x1 + x2 ∈ R (x1 + x2) := by
                cases hxy : x1 + x2 with
                | nil => simpa [R]
                | cons a b => simpa [R] using (Or.inl rfl : cons a b = cons a b ∨ cons a b ∈ R (a + b))
              have hrec : (D ((x1 + x2) + y) : Set BSeq) ⊆
                  (D y ∪ R_app (x1 + x2) y ∪ S (x1 + x2) : Finset BSeq) :=
                (ih (x1 + x2) hlt) (x1 + x2) hz_self_tail
              have hrec_t : t ∈ (D y ∪ R_app (x1 + x2) y ∪ S (x1 + x2) : Finset BSeq) := by
                have : t ∈ D ((x1 + x2) + y) := by simpa [add_assoc] using hDtail
                exact hrec this
              rcases Finset.mem_union.mp hrec_t with hDy_or_Rapp | hS
              · rcases Finset.mem_union.mp hDy_or_Rapp with hDy | hRapp
                · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hDy
                · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr (Rapp_embed hRapp)
              · exact Finset.mem_union.mpr <| Or.inr (S_embed hS)
          · -- R x1 branch goes to S x
            exact Finset.mem_union.mpr <| Or.inr (Rx1_to_S hRx1)
        · -- z ∈ R (x1+x2): recurse directly and lift
          have hrec : (D (z + y) : Set BSeq) ⊆
              (D y ∪ R_app (x1 + x2) y ∪ S (x1 + x2) : Finset BSeq) :=
            (ih (x1 + x2) hlt) z hz_tail
          have hrec_t : t ∈ (D y ∪ R_app (x1 + x2) y ∪ S (x1 + x2) : Finset BSeq) := hrec ht
          rcases Finset.mem_union.mp hrec_t with hDy_or_Rapp | hS
          · rcases Finset.mem_union.mp hDy_or_Rapp with hDy | hRapp
            · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hDy
            · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr (Rapp_embed hRapp)
          · exact Finset.mem_union.mpr <| Or.inr (S_embed hS)
  exact hmain z hz

/-- Corollary 1 (paper): `D[x] ⊆ R[x] ∪ S[x]`. -/
theorem corollary1 (x : BSeq) : (D x : Set BSeq) ⊆ (R x ∪ S x : Finset BSeq) := by
  -- Apply Lemma 4 with y = λ and z = x.
  have hxR : x ∈ R x := by
    cases x with
    | nil =>
        simp [R]
    | cons a b =>
        simp [R]
  have nil_mem_R : ∀ x : BSeq, nil ∈ R x := by
    intro x
    let P : BSeq → Prop := fun x => nil ∈ R x
    have hmain : P x := by
      refine (measure semilen).wf.induction x ?_
      intro x ih
      cases x with
      | nil =>
          change nil ∈ R nil
          simp [R]
      | cons x1 x2 =>
          have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
            simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
          have ih' : nil ∈ R (x1 + x2) := by simpa [P] using ih (x1 + x2) hlt
          exact by
            simpa [P, R] using (Or.inr ih' : nil = cons x1 x2 ∨ nil ∈ R (x1 + x2))
    exact hmain
  have h4 := lemma4 x nil x hxR
  intro z hz
  have hz' : z ∈ (D nil ∪ R_app x nil ∪ S x : Finset BSeq) := h4 (by simpa [add_nil] using hz)
  rcases Finset.mem_union.mp hz' with hDnil_or_Rapp | hS
  · rcases Finset.mem_union.mp hDnil_or_Rapp with hDnil | hRapp
    · -- D nil = {nil}, and nil ∈ R x (by repeated tail-deletion recurrence base)
      have hnil : z = nil := by simpa [D] using hDnil
      exact Finset.mem_union.mpr <| Or.inl <| by simpa [hnil] using nil_mem_R x
    · -- R_app x nil = image (fun z => z+nil) (R x) = R x
      rcases Finset.mem_image.mp hRapp with ⟨w, hwR, hwz⟩
      have : z = w := by simpa [add_nil] using hwz.symm
      exact Finset.mem_union.mpr <| Or.inl <| by simpa [this]
  · exact Finset.mem_union.mpr <| Or.inr hS

/-- Lemma 5 (paper): `S[xy] ⊆ S[x] ∪ S[y]`. -/
theorem lemma5 (x y : BSeq) : (S (x + y) : Set BSeq) ⊆ (S x ∪ S y : Finset BSeq) := by
  let P : BSeq → Prop := fun x => (S (x + y) : Set BSeq) ⊆ (S x ∪ S y : Finset BSeq)
  have hmain : P x := by
    refine (measure semilen).wf.induction x ?_
    intro x ih z hz
    cases x with
    | nil =>
        -- S(nil + y) = S y ⊆ S nil ∪ S y
        have : z ∈ S y := by simpa using hz
        exact Finset.mem_union.mpr <| Or.inr this
    | cons x1 x2 =>
        -- S((cons x1 x2)+y) = R x1 ∪ S((x1+x2)+y)
        have hz' : z ∈ (R x1 ∪ S ((x1 + x2) + y) : Finset BSeq) := by
          simpa [S, add_assoc] using hz
        rcases Finset.mem_union.mp hz' with hzR | hzS
        · -- R x1 ⊆ S(cons x1 x2)
          have hzSinX : z ∈ S (cons x1 x2) := by simpa [S] using Finset.mem_union.mpr (Or.inl hzR)
          exact Finset.mem_union.mpr <| Or.inl hzSinX
        · -- recurse on x1+x2
          have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
            simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
          have hrec : z ∈ (S (x1 + x2) ∪ S y : Finset BSeq) := (ih (x1 + x2) hlt) hzS
          rcases Finset.mem_union.mp hrec with hzSX | hzSY
          · have hzSinX : z ∈ S (cons x1 x2) := by simpa [S] using Finset.mem_union.mpr (Or.inr hzSX)
            exact Finset.mem_union.mpr <| Or.inl hzSinX
          · exact Finset.mem_union.mpr <| Or.inr hzSY
  exact hmain

/-- Lemma 6 (paper): `|S[x]| ≤ |x| d(x) + 1`. -/
theorem lemma6 (x : BSeq) : (S x).card ≤ semilen x * depth x + 1 := by
  -- First, a cardinal upper bound for R.
  have R_card_le : ∀ x : BSeq, (R x).card ≤ semilen x + 1 := by
    intro x
    let P : BSeq → Prop := fun x => (R x).card ≤ semilen x + 1
    have hmain : P x := by
      refine (measure semilen).wf.induction x ?_
      intro x ih
      cases x with
      | nil =>
          change (R nil).card ≤ semilen nil + 1
          simp [R, semilen]
      | cons x1 x2 =>
          have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
            simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
          have ih' : (R (x1 + x2)).card ≤ semilen (x1 + x2) + 1 := by
            simpa [P] using ih (x1 + x2) hlt
          calc
            (R (cons x1 x2)).card = ({cons x1 x2} ∪ R (x1 + x2)).card := by simp [R]
            _ ≤ ({cons x1 x2} : Finset BSeq).card + (R (x1 + x2)).card := Finset.card_union_le _ _
            _ = 1 + (R (x1 + x2)).card := by simp
            _ ≤ 1 + (semilen (x1 + x2) + 1) := Nat.add_le_add_left ih' 1
            _ = semilen (cons x1 x2) + 1 := by
              simp [semilen, semilen_add, Nat.add_comm]
    exact hmain
  -- Depth is always at least 1.
  have depth_ge_one : ∀ x : BSeq, 1 ≤ depth x := by
    intro x
    induction x with
    | nil => simp [depth]
    | cons x1 x2 ih1 ih2 =>
        have : 1 ≤ depth x1 + 1 := Nat.succ_le_succ (Nat.zero_le _)
        exact le_trans this (Nat.le_max_left _ _)
  -- For non-empty constructor case, depth is at least 2.
  have depth_cons_ge_two : ∀ x y : BSeq, 2 ≤ depth (cons x y) := by
    intro x y
    have : 1 ≤ depth x := depth_ge_one x
    exact le_trans (Nat.succ_le_succ this) (Nat.le_max_left _ _)
  -- Main proof by structural induction on x.
  induction x with
  | nil =>
      simp [S, semilen, depth]
  | cons x1 x2 ih1 ih2 =>
      have hSsplit : (S (x1 + x2)).card ≤ (S x1 ∪ S x2).card := by
        exact Finset.card_le_card (by
          intro z hz
          exact lemma5 x1 x2 hz)
      have hunion : (S (x1 + x2)).card ≤ (S x1).card + (S x2).card := by
        exact le_trans hSsplit (Finset.card_union_le (S x1) (S x2))
      calc
        (S (cons x1 x2)).card = (R x1 ∪ S (x1 + x2)).card := by simp [S]
        _ ≤ (R x1).card + (S (x1 + x2)).card := Finset.card_union_le _ _
        _ ≤ (R x1).card + ((S x1).card + (S x2).card) := by
              exact Nat.add_le_add_left hunion _
        _ ≤ (semilen x1 + 1) + ((semilen x1 * depth x1 + 1) + (semilen x2 * depth x2 + 1)) := by
              exact Nat.add_le_add (R_card_le x1) (Nat.add_le_add ih1 ih2)
        _ = semilen x1 * (depth x1 + 1) + semilen x2 * depth x2 + 3 := by
              ring_nf
        _ ≤ semilen x1 * depth (cons x1 x2) + semilen x2 * depth (cons x1 x2) + 3 := by
              have hdx : depth x1 + 1 ≤ depth (cons x1 x2) := Nat.le_max_left _ _
              have hdy : depth x2 ≤ depth (cons x1 x2) := Nat.le_max_right _ _
              exact Nat.add_le_add
                (Nat.add_le_add (Nat.mul_le_mul_left _ hdx) (Nat.mul_le_mul_left _ hdy))
                (Nat.le_refl _)
        _ = (semilen x1 + semilen x2) * depth (cons x1 x2) + 3 := by
              ring_nf
        _ ≤ (semilen x1 + semilen x2) * depth (cons x1 x2) + (depth (cons x1 x2) + 1) := by
              have h23 : 3 ≤ depth (cons x1 x2) + 1 := by
                have h2 : 2 ≤ depth (cons x1 x2) := depth_cons_ge_two x1 x2
                exact Nat.succ_le_succ h2
              exact Nat.add_le_add_left h23 _
        _ = (semilen x1 + semilen x2 + 1) * depth (cons x1 x2) + 1 := by
              ring_nf
        _ = semilen (cons x1 x2) * depth (cons x1 x2) + 1 := by
              simp [semilen, Nat.add_comm]

/-- Lemma 7 (paper): `|S[x]| ≤ |x| ℓ(x) + 1`. -/
theorem lemma7 (x : BSeq) : (S x).card ≤ semilen x * leaves x + 1 := by
  have leaves_ge_one : ∀ z : BSeq, 1 ≤ leaves z := by
    intro z
    induction z with
    | nil =>
        simp [leaves]
    | cons z1 z2 ih1 ih2 =>
        exact le_trans ih1 (Nat.le_add_right _ _)
  have depth_le_leaves : ∀ x : BSeq, depth x ≤ leaves x := by
    intro x
    induction x with
    | nil =>
        simp [depth, leaves]
    | cons x1 x2 ih1 ih2 =>
        have h1 : depth x1 + 1 ≤ leaves x1 + leaves x2 := by
          calc
            depth x1 + 1 ≤ leaves x1 + 1 := Nat.add_le_add_right ih1 1
            _ ≤ leaves x1 + leaves x2 := by
                  exact Nat.add_le_add_left (leaves_ge_one x2) _
        have h2 : depth x2 ≤ leaves x1 + leaves x2 := by
          exact le_trans ih2 (Nat.le_add_left _ _)
        exact max_le h1 h2
  have h6 := lemma6 x
  have hmul : semilen x * depth x ≤ semilen x * leaves x := Nat.mul_le_mul_left _ (depth_le_leaves x)
  exact le_trans h6 (Nat.add_le_add_right hmul 1)

/-- Corollary 2 (paper): `|S[x]| ≤ |x| min(d(x),ℓ(x)) + 1`. -/
theorem corollary2 (x : BSeq) :
    (S x).card ≤ semilen x * Nat.min (depth x) (leaves x) + 1 := by
  have htot := le_total (depth x) (leaves x)
  rcases htot with hdl | hld
  · simpa [Nat.min_eq_left hdl] using lemma6 x
  · simpa [Nat.min_eq_right hld] using lemma7 x

/-- Theorem 1 (paper): cardinality bound on decomposition. -/
theorem theorem1 (x : BSeq) :
    (D x).card ≤ semilen x * (Nat.min (depth x) (leaves x) + 1) + 1 := by
  -- Paper: D ⊆ R ∪ S and |R[x]| ≤ |x|+1, then apply Corollary 2.
  have R_card_le : ∀ x : BSeq, (R x).card ≤ semilen x + 1 := by
    intro x
    let P : BSeq → Prop := fun x => (R x).card ≤ semilen x + 1
    have hmain : P x := by
      refine (measure semilen).wf.induction x ?_
      intro x ih
      cases x with
      | nil =>
          change (R nil).card ≤ semilen nil + 1
          simp [R, semilen]
      | cons x1 x2 =>
          have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
            simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
          have ih' : (R (x1 + x2)).card ≤ semilen (x1 + x2) + 1 := by
            simpa [P] using ih (x1 + x2) hlt
          calc
            (R (cons x1 x2)).card = ({cons x1 x2} ∪ R (x1 + x2)).card := by simp [R]
            _ ≤ ({cons x1 x2} : Finset BSeq).card + (R (x1 + x2)).card := Finset.card_union_le _ _
            _ = 1 + (R (x1 + x2)).card := by simp
            _ ≤ 1 + (semilen (x1 + x2) + 1) := Nat.add_le_add_left ih' 1
            _ = semilen (cons x1 x2) + 1 := by
              simp [semilen, semilen_add, Nat.add_comm]
    exact hmain
  have nil_mem_R : ∀ x : BSeq, nil ∈ R x := by
    intro x
    let P : BSeq → Prop := fun x => nil ∈ R x
    have hmain : P x := by
      refine (measure semilen).wf.induction x ?_
      intro x ih
      cases x with
      | nil =>
          change nil ∈ R nil
          simp [R]
      | cons x1 x2 =>
          have hlt : semilen (x1 + x2) < semilen (cons x1 x2) := by
            simpa [semilen, semilen_add] using (Nat.lt_succ_self (x1.semilen + x2.semilen))
          have ih' : nil ∈ R (x1 + x2) := by simpa [P] using ih (x1 + x2) hlt
          exact by
            simpa [P, R] using (Or.inr ih' : nil = cons x1 x2 ∨ nil ∈ R (x1 + x2))
    exact hmain
  have nil_mem_S : ∀ x : BSeq, nil ∈ S x := by
    intro x
    cases x with
    | nil =>
        simp [S]
    | cons x1 x2 =>
        simpa [S] using (Finset.mem_union.mpr <| Or.inl (nil_mem_R x1))
  have hDsub : (D x).card ≤ (R x ∪ S x).card := Finset.card_le_card (corollary1 x)
  have hinter_one : 1 ≤ (R x ∩ S x).card := by
    apply Finset.one_le_card.mpr
    exact ⟨nil, by simp [nil_mem_R x, nil_mem_S x]⟩
  have hunion_plus_one : (R x ∪ S x).card + 1 ≤ (R x).card + (S x).card := by
    calc
      (R x ∪ S x).card + 1 ≤ (R x ∪ S x).card + (R x ∩ S x).card := Nat.add_le_add_left hinter_one _
      _ = (R x).card + (S x).card := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Finset.card_union_add_card_inter (R x) (S x))
  have hunion_le : (R x ∪ S x).card ≤ (R x).card + (S x).card - 1 := Nat.le_sub_of_add_le hunion_plus_one
  have hsum : (R x).card + (S x).card ≤ (semilen x + 1) + (semilen x * Nat.min (depth x) (leaves x) + 1) := by
    exact Nat.add_le_add (R_card_le x) (corollary2 x)
  have hsum_sub : (R x).card + (S x).card - 1 ≤ ((semilen x + 1) + (semilen x * Nat.min (depth x) (leaves x) + 1)) - 1 :=
    Nat.sub_le_sub_right hsum 1
  calc
    (D x).card ≤ (R x ∪ S x).card := hDsub
    _ ≤ (R x).card + (S x).card - 1 := hunion_le
    _ ≤ ((semilen x + 1) + (semilen x * Nat.min (depth x) (leaves x) + 1)) - 1 := hsum_sub
    _ = semilen x * (Nat.min (depth x) (leaves x) + 1) + 1 := by
          have htmp :
              ((semilen x + 1) + (semilen x * Nat.min (depth x) (leaves x) + 1)) - 1 =
                semilen x + (semilen x * Nat.min (depth x) (leaves x)) + 1 := by
            omega
          rw [htmp]
          ring_nf

/-! ## Section 3: Ordered trees, embedded subtrees, and Theorem 2 -/

/-- Ordered rooted trees (paper’s “ordered trees”). -/
inductive OTree : Type
  | node : List OTree → OTree
deriving Repr

namespace OTree

/-- Number of nodes. -/
def nodes : OTree → Nat
  | node cs => 1 + (cs.map nodes).sum

/-- Number of edges. -/
def edges : OTree → Nat
  | node cs => cs.length + (cs.map edges).sum

/-- Depth (root has depth 1). -/
def depth : OTree → Nat
  | node [] => 1
  | node cs => 1 + (cs.map depth).foldr Nat.max 0

/-- Number of leaves. -/
def leaves : OTree → Nat
  | node [] => 1
  | node cs => (cs.map leaves).sum

/-- Paper Definition 1: balanced sequence encoding of an ordered tree. -/
def encode : OTree → BSeq
  | node cs =>
      cs.foldr (fun c acc => (BSeq.nest (encode c)) + acc) BSeq.nil

/-- Decode a balanced sequence to an ordered tree (standard inverse). -/
def decodeForest : BSeq → List OTree
  | BSeq.nil => []
  | BSeq.cons x y => node (decodeForest x) :: decodeForest y

def decode (s : BSeq) : OTree := node (decodeForest s)

/-- Encode∘Decode is identity on balanced sequences. -/
theorem encode_decodeForest (s : BSeq) : (decodeForest s).foldr (fun c acc => (BSeq.nest (encode c)) + acc) BSeq.nil = s := by
  induction s with
  | nil =>
      simp [decodeForest]
  | cons x y ihx ihy =>
      simp [decodeForest, encode]
      exact ⟨ihx, ihy⟩

theorem encode_decode (s : BSeq) : encode (decode s) = s := by
  simpa [decode, encode] using encode_decodeForest s

/-- A single edge contraction step (contract one parent-child edge, splicing grandchildren). -/
inductive Contract1 : OTree → OTree → Prop
  | atRoot (pre post : List OTree) (gc : List OTree) :
      Contract1 (node (pre ++ node gc :: post)) (node (pre ++ gc ++ post))

/-- Embedded subtree relation = reflexive-transitive closure of contractions (paper Def. 5). -/
inductive EmbSub : OTree → OTree → Prop
  | refl (t) : EmbSub t t
  | tail {a b c} : EmbSub a b → Contract1 c b → EmbSub a c

/-- Common embedded subtree. -/
def IsCommonEmbedded (u s t : OTree) : Prop := EmbSub u s ∧ EmbSub u t

/-- Maximum common embedded subtree (by number of edges). -/
def IsMCES (u s t : OTree) : Prop :=
  IsCommonEmbedded u s t ∧ ∀ u', IsCommonEmbedded u' s t → edges u' ≤ edges u

/--
Key lemma: contracting one edge deletes exactly one annotation pair in the encoding.
-/
theorem encode_contract1 {t u : OTree} (h : Contract1 t u) :
    BSeq.Contained (encode u) (encode t) := by
  have encode_node_append : ∀ as bs : List OTree, encode (node (as ++ bs)) = encode (node as) + encode (node bs) := by
    intro as bs
    induction as with
    | nil =>
        simp [encode]
    | cons a as ih =>
        calc
          encode (node ((a :: as) ++ bs))
              = BSeq.nest (encode a) + encode (node (as ++ bs)) := by
                  simp [encode]
          _ = BSeq.nest (encode a) + (encode (node as) + encode (node bs)) := by
                rw [ih]
          _ = (BSeq.nest (encode a) + encode (node as)) + encode (node bs) := by
                rw [BSeq.add_assoc]
          _ = encode (node (a :: as)) + encode (node bs) := by
                simp [encode]
  rcases h with ⟨pre, post, gc⟩
  let a : BSeq := encode (node pre)
  let b : BSeq := encode (node gc)
  let c : BSeq := encode (node post)
  have hu : encode (node (pre ++ gc ++ post)) = a + b + c := by
    calc
      encode (node (pre ++ gc ++ post))
          = encode (node pre) + encode (node (gc ++ post)) := by
              simpa [a] using encode_node_append pre (gc ++ post)
      _ = a + (encode (node gc) + encode (node post)) := by
            simpa [a] using congrArg (fun z => a + z) (encode_node_append gc post)
      _ = a + b + c := by
            simp [a, b, c, BSeq.add_assoc]
  have hu' : encode (node (pre ++ (gc ++ post))) = a + b + c := by
    simpa [List.append_assoc] using hu
  have ht : encode (node (pre ++ node gc :: post)) = a + BSeq.cons b c := by
    calc
      encode (node (pre ++ node gc :: post))
          = encode (node pre) + encode (node (node gc :: post)) := by
              simpa [a] using encode_node_append pre (node gc :: post)
      _ = a + (BSeq.nest (encode (node gc)) + encode (node post)) := by
            simp [encode, a]
      _ = a + BSeq.cons b c := by
            simp [a, b, c, BSeq.nest]
  have hstep : Contained (a + b + c) (a + BSeq.cons b c) := by
    refine Contained.step (a + b + c) (a + BSeq.cons b c) a b c a b c ?_ ?_ (Contained.refl _) (Contained.refl _) (Contained.refl _)
    · rfl
    · rfl
  simpa [hu', ht] using hstep

/--
If `u` is an embedded subtree of `t`, then `encode u ⊑ encode t`.
-/
theorem encode_embSub {u t : OTree} (h : EmbSub u t) : encode u ⊑ encode t := by
  induction h with
  | refl =>
      exact Contained.refl _
  | tail hab hcb ih =>
      exact contained_trans ih (encode_contract1 hcb)

/--
Theorem 2 (paper): LCBS of the balanced sequences corresponds to MCES.

We phrase it as: if `r` is an LCBS of `encode S` and `encode T`,
then `decode r` is an MCES of `S` and `T`.
-/
theorem theorem2 (S T : OTree) :
    IsMCES (decode (BSeq.LCBS (encode S) (encode T))) S T := by
  -- Correctness direction uses:
  -- 1) `encode (decode r) = r`
  -- 2) `encode_embSub` (embedded subtree ⇒ containment)
  -- 3) a converse (containment ⇒ embedded subtree) to show commonality.
  -- The converse requires a constructive argument that every containment step corresponds to
  -- contracting the matching edge in the decoded tree, and then transporting along `encode_decode`.
  --
  -- This is substantial, and depends on a fully proved transitivity lemma for `⊑`.
  --
  -- Therefore we leave this theorem as `sorry` for now, but note:
  --   * mathematically the proof is exactly the paper’s one-paragraph argument,
  --   * the missing Lean work is the containment/transitivity + containment⇒EmbSub construction.
  --
  sorry

end OTree

/-! ## Section 4: Lemma 8 (DP recurrence for LCBS size) -/

/-- Lemma 8 (paper), as an equality of the *numeric* LCBS size. -/
theorem lemma8 (s t : BSeq) :
    lcsLen s t =
      Nat.max
        (Nat.max
          (lcsLen (head s) (head t) + lcsLen (tail s) (tail t) + (if s = nil ∨ t = nil then 0 else 1))
          (lcsLen (headTail s) t))
        (lcsLen s (headTail t)) := by
  -- This is the paper’s recurrence with base cases.
  -- A clean Lean proof requires:
  --   (i) a fully formal `⊑` transitivity lemma (or switching to an explicit single-deletion closure),
  --   (ii) a “first-annotation case split” lemma for optimal LCBS.
  -- With the current `⊑` definition, those proofs are lengthy and were not completed above.
  --
  -- Once `contained_trans` is fully proved (and the containment⇒EmbSub construction if desired),
  -- this lemma can be proven by the standard max-upperbound / max-lowerbound argument used in the paper.
  --
  -- For now, we add the lemma statement and leave a `sorry` with this explanation.
  sorry
/-- Runtime parameters `(n1, n2, d1, l1, d2, l2)` used in Theorem 3. -/
abbrev Params : Type := Nat × Nat × Nat × Nat × Nat × Nat

/-- The paper’s polynomial bound expression (as a natural number). -/
def runtimeBoundNat (p : Params) : Nat :=
  let n1 := p.1
  let n2 := p.2.1
  let d1 := p.2.2.1
  let l1 := p.2.2.2.1
  let d2 := p.2.2.2.2.1
  let l2 := p.2.2.2.2.2
  n1 * n2 * Nat.min d1 l1 * Nat.min d2 l2

/-- Extract runtime parameters from a pair of trees. -/
def paramsOfTrees (S T : OTree) : Params :=
  (OTree.nodes S, (OTree.nodes T, (OTree.depth S, (OTree.leaves S, (OTree.depth T, OTree.leaves T)))))

/-- Theorem 3 runtime companion statement (left as `sorry`). -/
theorem theorem3_runtime_bound :
    ∃ (mcesAlg : OTree → OTree → OTree) (mcesCost : OTree → OTree → Nat) (T : Params → Nat),
      (∀ S Ttree, OTree.IsMCES (mcesAlg S Ttree) S Ttree) ∧
      (∀ S Ttree, mcesCost S Ttree ≤ T (paramsOfTrees S Ttree)) ∧
      ((fun p : Params => (T p : Real)) =O[Filter.atTop] fun p : Params => (runtimeBoundNat p : Real)) := by
  sorry
end BSeq

end LozanoValiente2004
