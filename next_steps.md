# Next Steps: Unconditional Tree-Leaf Lemma 7 -> Theorem 3

**Timestamp (UTC): 2026-03-01T04:59:02Z**

## Objective
Finish the remaining combinatorial gap in `Lozano-v6` so the tree-leaf pipeline is unconditional:

1. Prove tree-leaf Lemma 7 (or a formally acceptable slack variant),
2. make tree-leaf Corollary 2 + Theorem 1 unconditional,
3. instantiate the existing Theorem 3 runtime wrappers with no extra hypotheses.

## Current Build / Health

- File compiles:
  - `cd proofs && lake build SubtreeProofs/Lozano-v6.lean`
  - Last status: `Build completed successfully (3123 jobs).`
- No `sorry` in `Lozano-v6.lean` (only the string in a status comment).

## Key File

- Main file: `/home/joncrall/code/networkx_algo_common_subtree/proofs/SubtreeProofs/Lozano-v6.lean`

## What Was Completed (Important Context)

### 1) Requested `leavesPairOfSeq` helper lemmas (with simp)

- `treeLeavesOfSeq_nil` at line 1120
- `forestLeavesOfSeq_nil` at line 1124
- `treeLeavesOfSeq_cons` at line 1128
- `forestLeavesOfSeq_cons` at line 1133
- `forestLeavesOfSeq_cons_eq_treeLeavesOfSeq_cons` at line 1138

### 2) Decomposition/set bridge lemmas for degenerate tail analysis

- `R_subset_D` at line 568
- `S_subset_D` at line 591
- `D_eq_R_union_S` at line 616
- `S_cons_nil_eq_D` at line 628

These are important because the degenerate branch rewrites through `S (cons x nil) = D x`.

### 3) Non-degenerate branch of tree-leaf Lemma 7 is proved

- `lemma7_tree_cons_of_cons_tail` at line 1274
  - Handles `S (cons x (cons y1 y2))` using `lemma5` + `R_card_le` + arithmetic.

### 4) Full Lemma 7 reduced to one degenerate-tail obligation

- `lemma7_tree_of_nil_tail_bound` at line 1372:
  - If you can prove:
    - `hnil : ∀ x, (S (cons x nil)).card ≤ semilen (cons x nil) * treeLeavesOfSeq (cons x nil) + 1`
  - then you get:
    - `∀ x, (S x).card ≤ semilen x * treeLeavesOfSeq x + 1`.

### 5) Runtime pipeline already wired to the reduced obligation

- `theorem3_runtime_concrete_of_nil_tail_bound` (BSeq) at line 2170
- `theorem3_runtime_bound_of_nil_tail_bound` (BSeq) at line 2364
- top-level aliases:
  - `theorem3_runtime_concrete_of_nil_tail_bound` at line 2497
  - `theorem3_runtime_bound_of_nil_tail_bound` at line 2509

So once `hnil` is proved, Theorem 3 wrappers are effectively ready.

## Remaining Blocker (Single Critical Gap)

Prove:

```lean
∀ x : BSeq,
  (S (BSeq.cons x BSeq.nil)).card ≤
    semilen (BSeq.cons x BSeq.nil) * treeLeavesOfSeq (BSeq.cons x BSeq.nil) + 1
```

This is the only missing ingredient to make:

- `lemma7_tree` unconditional,
- `corollary2_treeLeaves_of_lemma7_tree` unconditional,
- `theorem1_treeLeaves_of_lemma7_tree` unconditional,
- `theorem3_runtime_concrete_of_lemma7_tree` / `..._bound_of_lemma7_tree` unconditional.

## Recommended Plan (Smallest-Leverage First)

### Step 1: Isolate a standalone theorem for the nil-tail branch

Create a theorem near line ~1372:

```lean
theorem lemma7_tree_nil_tail
  (x : BSeq) :
  (S (BSeq.cons x BSeq.nil)).card ≤
    semilen (BSeq.cons x BSeq.nil) * treeLeavesOfSeq (BSeq.cons x BSeq.nil) + 1 := by
  ...
```

Then:

```lean
have h7tree := lemma7_tree_of_nil_tail_bound (fun x => lemma7_tree_nil_tail x)
```

### Step 2: Use the `S_cons_nil_eq_D` rewrite immediately

First line in proof should rewrite:

```lean
rw [S_cons_nil_eq_D]
```

Goal becomes a `D x` cardinal bound.

### Step 3: Prove a `D` cardinal bound specialized to the needed shape

Likely target:

```lean
(D x).card ≤ (semilen x + 1) * treeLeavesOfSeq x + 1
```

because

```lean
semilen (cons x nil) = semilen x + 1
treeLeavesOfSeq (cons x nil) = treeLeavesOfSeq x
```

Possible methods:
- Direct measure induction on `x`,
- split `x = nil | cons a b`,
- exploit existing decomposition lemmas (`lemma1..lemma5`, `corollary1`, `R_card_le`) and the new set bridges.

### Step 4: Instantiate the reduction and close the chain

After proving `lemma7_tree_nil_tail`:

1. define unconditional `lemma7_tree`,
2. derive unconditional tree-leaf Corollary 2 and Theorem 1 using existing scaffolding,
3. add unconditional Theorem 3 wrappers by applying:
   - `theorem3_runtime_concrete_of_lemma7_tree`,
   - `theorem3_runtime_bound_of_lemma7_tree`.

### Step 5: Cleanup / hardening

- Replace local duplicated `R_card_le` inside `theorem1_of_corollary2_bound` with the global theorem if convenient.
- Keep build green after each mini-lemma.

## Alternative (If Exact Constant Stalls)

User allowed slack variants if needed for same Big-O.

Fallback option:

1. Prove a slack nil-tail inequality (e.g. factor 2),
2. lift through a slack `lemma7_tree` theorem,
3. adjust runtime constants in Theorem 3 wrappers.

Do this only if exact nil-tail constant is intractable; exact is preferred.

## Useful Existing Bridge Theorems

- `corollary2_treeLeaves_of_lemma7_tree` line 1408
- `theorem1_treeLeaves_of_lemma7_tree` line 1504
- `kappa_le_kappaBoundSeqTree` line 1741
- `theorem3_runtime_concrete_of_theorem1_treeLeaves` line 2137
- `theorem3_runtime_concrete_of_lemma7_tree` line 2154
- `theorem3_runtime_bound_of_lemma7_tree` line 2347

## Helpful Commands

```bash
# compile target file
cd proofs && lake build SubtreeProofs/Lozano-v6.lean

# find relevant theorem locations
rg -n "lemma7_tree|nil_tail|S_cons_nil_eq_D|theorem3_runtime_concrete_of_nil_tail_bound" proofs/SubtreeProofs/Lozano-v6.lean
```

## Notes from Recent Proof Engineering Failures

- Don’t put `have` declarations directly as `calc` steps.
- For `WellFounded.induction` over `∀ x, ...`, using `let P` + `have hmain : P x` is often required to avoid motive mismatch.
- Keep simp argument lists minimal; linter catches stale simp args quickly.

