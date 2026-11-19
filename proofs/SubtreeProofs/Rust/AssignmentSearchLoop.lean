module

public import SubtreeProofs.Rust.AssignmentSearchBody
import Mathlib.Tactic

/-!
# Complete actual augmenting-column search

The generated Rust loop terminates successfully from an independent unfinished
partial matching and feasible/tight numeric state. It returns a real unmatched
column, preserves all old matching tightness and numeric invariants, and
constructs a finite ranked tight predecessor forest for actual augmentation.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentSearchLoop

open AssignmentInitialization AssignmentColumnScan AssignmentScanInvariant AssignmentAdjustmentInvariant
open AssignmentSearchArithmetic AssignmentSearchInvariant AssignmentSearchTransition AssignmentSearchBody
open AssignmentPredecessorPaths AssignmentDiscoveryRanks AssignmentPredecessorTightness

structure Found (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n : Usize) (initialRows : Fin n.val → ℤ)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize) : Prop where
  u_len : n.val < u.length
  v_len : n.val < v.length
  predecessor_len : n.val < predecessor.length
  column_positive : 0 < column.val
  column_bound : column.val ≤ n.val
  free : matched.val[column.val]!.val = 0
  potential : PotentialInvariant cost n initialRows u v
  matching_tight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
    (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (fun col => matched.val[col]!.val)
  forest : ∃ vertices : Finset Nat, ∃ rank : Nat → Nat, column.val ∈ vertices ∧
    Ranked (alloc.vec.Vec.deref predecessor) n vertices rank ∧ ForestTight cost u v matched (alloc.vec.Vec.deref predecessor) vertices

def SearchFinished (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n : Usize)
    (initialRows : Fin n.val → ℤ) (output : SearchOutput) : Prop :=
  let (u,v,predecessor,column,failure) := output
  failure = none ∧ Found cost matched n initialRows u v predecessor column

/-- A stopped valid search has found the required free real column and its
finite ranked tight predecessor forest. -/
theorem found_of_invariant (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize)
    (h : Invariant cost matched n initialRows u v predecessor column slack used visited false none) :
    Found cost matched n initialRows u v predecessor column := by
  have hfree : matched.val[column.val]!.val = 0 := by
    by_contra hn
    have hh := h.searching_exact.mpr hn
    exact Bool.noConfusion hh
  have hp : 0 < column.val := by
    by_contra hn
    have hz : column.val = 0 := by omega
    rw [hz,input.root] at hfree
    omega
  have hnew : column.val ∉ usedIndices (alloc.vec.Vec.deref used) (n.val+1) := by
    intro hm
    have hh := (mem_usedIndices (alloc.vec.Vec.deref used) _ _).mp hm
    simp only [alloc.vec.Vec.deref,Slice.from_val,h.column_free] at hh
    exact Bool.noConfusion hh.2
  obtain ⟨rank,hbound,hforest⟩ := h.ranked
  refine ⟨h.u_len,h.v_len,h.predecessor_len,hp,h.column_bound,hfree,h.potential,h.matching_tight,?_,?_,?_,?_⟩
  · exact insert column.val (usedIndices (alloc.vec.Vec.deref used) (n.val+1))
  · exact rank
  · exact Finset.mem_insert_self _ _
  · refine ⟨?_,?_⟩
    · apply ranked_terminal (alloc.vec.Vec.deref predecessor) n _ rank visited.val column.val hforest hbound h.column_bound hnew
      simpa only [alloc.vec.Vec.deref,Slice.from_val] using h.pending_predecessor (by omega)
    · apply forest_visit cost u v matched (alloc.vec.Vec.deref predecessor) _ column.val h.forest_tight
      intro hz
      simpa only [alloc.vec.Vec.deref,Slice.from_val] using h.pending_tight hz

/-- The actual complete generated loop terminates without an error branch;
its visit count strictly increases while bounded by finite matching capacity. -/
theorem find_augmenting_column_loop_spec (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize) (column : Usize)
    (slack : alloc.vec.Vec (Option I128)) (used : alloc.vec.Vec Bool) (visited : Usize) (searching : Bool) (failure : Option AssignmentError)
    (hinit : Invariant cost matched n initialRows u v predecessor column slack used visited searching failure) :
    find_augmenting_column_loop cost u v matched predecessor n column slack used visited searching failure ⦃ output =>
      SearchFinished cost matched n initialRows output ⦄ := by
  unfold find_augmenting_column_loop
  apply loop.spec_decr_nat (fun state => n.val-visitCount state) (StateInvariant cost matched n initialRows)
    (SearchFinished cost matched n initialRows) _ (u,v,predecessor,column,slack,used,visited,searching,failure) ?_ (by exact hinit)
  rintro ⟨currentU,currentV,currentPred,currentColumn,currentSlack,currentUsed,currentVisited,currentSearching,currentFailure⟩ hinv
  change Invariant cost matched n initialRows currentU currentV currentPred currentColumn currentSlack currentUsed currentVisited currentSearching currentFailure at hinv
  have hfailure := hinv.failure_none
  subst currentFailure
  cases currentSearching with
  | false =>
    apply WP.spec_mono (body_done_spec cost matched n currentU currentV currentPred currentColumn currentSlack currentUsed currentVisited)
    intro output houtput
    subst output
    exact ⟨rfl,found_of_invariant cost matched n extent filled initialRows input currentU currentV currentPred currentColumn currentSlack currentUsed currentVisited hinv⟩
  | true =>
    have hv := hinv.visit_guard cost matched n extent filled initialRows input currentU currentV currentPred currentColumn currentSlack currentUsed currentVisited true none rfl
    apply WP.spec_mono (body_running_spec cost matched n extent filled initialRows input currentU currentV currentPred currentColumn currentSlack currentUsed currentVisited hinv)
    rintro output ⟨next,houtput,hnext,hcount⟩
    subst output
    refine ⟨hnext,?_⟩
    change n.val-visitCount next < n.val-currentVisited.val
    omega

/-- Actual source search, including both local initialization loops, returns
a free real column and all independent invariants required by augmentation.
No local overflow/index bound, minimum, path or program-result certificate is
supplied to this endpoint. -/
theorem find_augmenting_column_spec (cost : Slice (alloc.vec.Vec I64)) (matched : Slice Usize) (n extent : Usize)
    (filled : Nat) (initialRows : Fin n.val → ℤ) (input : Input cost matched n extent filled initialRows)
    (u v : alloc.vec.Vec I128) (predecessor : alloc.vec.Vec Usize)
    (hu : n.val < u.length) (hv : n.val < v.length) (hp : n.val < predecessor.length)
    (hpotential : PotentialInvariant cost n initialRows u v)
    (htight : Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (fun col => matched.val[col]!.val)) :
    find_augmenting_column cost u v matched predecessor n extent ⦃ output => ∃ column : Usize,
      output.1 = core.result.Result.Ok column ∧
        Found cost matched n initialRows output.2.1 output.2.2.1 output.2.2.2 column ⦄ := by
  unfold find_augmenting_column
  apply WP.spec_bind (absent_costs_spec extent)
  intro slack hslack
  apply WP.spec_bind (unused_columns_spec extent)
  intro used hused
  have hinit := initial_invariant cost matched n extent filled initialRows input u v predecessor slack used hu hv hp hslack hused hpotential htight
  apply WP.spec_bind (find_augmenting_column_loop_spec cost matched n extent filled initialRows input u v predecessor 0#usize slack used 0#usize true none hinit)
  rintro ⟨finalU,finalV,finalPred,column,failure⟩ hfinished
  change failure = none ∧ Found cost matched n initialRows finalU finalV finalPred column at hfinished
  rcases hfinished with ⟨hfailure,hfound⟩
  subst failure
  simp only [uncurry_apply_pair,WP.spec_ok]
  exact ⟨column,rfl,hfound⟩

end SubtreeProofs.Rust.AssignmentSearchLoop

end
