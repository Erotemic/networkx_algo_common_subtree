module

public import SubtreeProofs.Rust.SourceEvalDerivedCalls

/-! The concrete helper dispatcher discharges local callee contracts on native
argument shapes and sufficient call-nesting fuel. These readiness conditions
contain inputs and depth bounds, never a desired helper/evaluator answer. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource LookupSource.Heap LookupSource.Partial LookupSource.Partial.Addressed Storage verified_ordered_core

inductive Ready (fuel : Nat) : SourceEval.Function → List ValueCell → Prop where
  | copyWord (word : BalancedWord) (pointer : Pointer) : wordHeight word ≤ fuel →
      Ready fuel .copyWord [(.shared pointer, .reference (encodeWord word))]
  | compare (left right : BalancedWord) (pl pr : Pointer) : wordHeight left ≤ fuel →
      Ready fuel .compare [(.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
  | copyResult (result : CommonEmbedding) (pointer : Pointer) : wordHeight result.word + 1 ≤ fuel →
      Ready fuel .copyResult [(.shared pointer, .reference (encodeResult result))]
  | lookup (table : MemoTable) (left right : BalancedWord) (pt pl pr : Pointer) : lookupDepth table left right ≤ fuel →
      Ready fuel .lookup [(.shared pt, .reference (encodeTable table)), (.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
  | concatenate (left right : BalancedWord) (pl pr : Pointer) : MemoSource.concatenateDepth left right ≤ fuel →
      Ready fuel .concatenate [(.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
  | insert (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (tc : Cell) (pl pr pc : Pointer) :
      MemoSource.insertDepth left right result ≤ fuel → Ready fuel .insert [(tc, encodeTable table),
        (.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right)), (.shared pc, .reference (encodeResult result))]
  | boxNew (cell : Cell) (value : Value) : 0 < fuel → Ready fuel .boxNew [(cell, value)]
  | checkedAdd (left right : Nat) : 0 < fuel → left < 2^32 → right < 2^32 →
      Ready fuel .checkedAdd [(.number left, .number left), (.number right, .number right)]

def callee (fuel budget : Nat) : Derived.Callees := fun world _ function packets => execute fuel budget world function packets

theorem packets_represented {memory : Memory} {live : Live} {packets : List ValueCell}
    (h : ∀ p ∈ packets, Readable memory live p.1 p.2) :
    RepresentsFields memory (packets.map Prod.fst) (packets.map Prod.snd) := by
  induction packets with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨_, hg, _⟩ := h head (by simp)
    exact .cons hg.represents (ih (fun p hm => h p (by simp [hm])))

theorem callee_respects (fuel budget : Nat) :
    Derived.CallsRespect (callee fuel budget) (SourceEval.run SourceEval.Certificate.original.body fuel)
      (fun _ function packets => Ready fuel function packets) := by
  intro world guards function packets final packet cost hw hp _ hready hrun
  have represented := packets_represented hp
  cases hready with
  | copyWord word pointer depth =>
    obtain ⟨oldCost, hs, _⟩ := LookupSource.copy_source word fuel depth
    have hs' : Control.run LookupSource.Certificate.original.body fuel .copyWord [.reference (encodeWord word)] = some (encodeWord word, oldCost) := by
      rwa [LookupSource.Certificate.original_run]
    obtain ⟨hs, hr, hf, hk⟩ := lookup_spec fuel budget hw .copyWord [(.shared pointer, .reference (encodeWord word))]
      (.cons (.reference (SourceEval.Helpers.word_bounded word)) .nil) represented hs' hrun
    exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | compare left right pl pr depth =>
    obtain ⟨oldCost, hs, _⟩ := LookupSource.compare_source left right fuel depth
    have hs' : Control.run LookupSource.Certificate.original.body fuel .compare
        [.reference (encodeWord left), .reference (encodeWord right)] = some (.boolean (LookupEvents.compare left right).1, oldCost) := by
      rwa [LookupSource.Certificate.original_run]
    obtain ⟨hs, hr, hf, hk⟩ := lookup_spec fuel budget hw .compare
      [(.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
      (.cons (.reference (SourceEval.Helpers.word_bounded left)) (.cons (.reference (SourceEval.Helpers.word_bounded right)) .nil)) represented hs' hrun
    exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | copyResult result pointer depth =>
    obtain ⟨oldCost, hs, _⟩ := LookupSource.copyResult_source result fuel depth
    have hs' : Control.run LookupSource.Certificate.original.body fuel .copyResult [.reference (encodeResult result)] = some (encodeResult result, oldCost) := by
      rwa [LookupSource.Certificate.original_run]
    obtain ⟨hs, hr, hf, hk⟩ := lookup_spec fuel budget hw .copyResult [(.shared pointer, .reference (encodeResult result))]
      (.cons (.reference (SourceEval.Helpers.result_bounded result)) .nil) represented hs' hrun
    exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | lookup table left right pt pl pr depth =>
    obtain ⟨oldCost, hs, _⟩ := LookupSource.lookup_source table left right fuel depth
    have hs' : Control.run LookupSource.Certificate.original.body fuel .lookup
        [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeOption (LookupEvents.lookup table left right).1, oldCost) := by
      rwa [LookupSource.Certificate.original_run]
    obtain ⟨hs, hr, hf, hk⟩ := lookup_spec fuel budget hw .lookup [(.shared pt, .reference (encodeTable table)),
      (.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
      (.cons (.reference (SourceEval.Helpers.table_bounded table)) (.cons (.reference (SourceEval.Helpers.word_bounded left))
        (.cons (.reference (SourceEval.Helpers.word_bounded right)) .nil))) represented hs' hrun
    exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | concatenate left right pl pr depth =>
    obtain ⟨oldCost, hs, _⟩ := MemoSource.concatenate_source left right fuel depth
    have hs' : MemoSource.sourceRun MemoSource.Certificate.original.body fuel .concatenate
        [.reference (encodeWord left), .reference (encodeWord right)] = some (encodeWord (OrderedSolver.appendWord left right), oldCost) := by
      rwa [MemoSource.Certificate.original_run]
    obtain ⟨hs, hr, hf, hk⟩ := memo_spec fuel budget hw .concatenate
      [(.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
      (.cons (.reference (SourceEval.Helpers.word_bounded left)) (.cons (.reference (SourceEval.Helpers.word_bounded right)) .nil)) represented hs' hrun
    exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | insert table left right result tc pl pr pc depth =>
    obtain ⟨oldCost, hs, _⟩ := MemoSource.insert_source table left right result fuel depth
    have hs' : MemoSource.sourceRun MemoSource.Certificate.original.body fuel .insert
        [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), oldCost) := by
      rwa [MemoSource.Certificate.original_run]
    obtain ⟨hs, hr, hf, hk⟩ := memo_spec fuel budget hw .insert [(tc, encodeTable table),
      (.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right)), (.shared pc, .reference (encodeResult result))]
      (.cons (SourceEval.Helpers.table_bounded table) (.cons (.reference (SourceEval.Helpers.word_bounded left))
        (.cons (.reference (SourceEval.Helpers.word_bounded right)) (.cons (.reference (SourceEval.Helpers.result_bounded result)) .nil)))) represented hs' hrun
    exact ⟨hs, hr, hf, (hk guards).preserves⟩
  | boxNew cell value positive =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h := boxNew_total fuel hw (hp (cell, value) (by simp))
      have hr : boxNew (fuel + 1) world [(cell, value)] = some (final, packet, cost) := hrun
      rw [h.1] at hr
      obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
      exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, (h.2.2.2.2.1 guards).preserves⟩
  | checkedAdd left right positive hl hr =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h := checkedAdd_total fuel hw left right hl hr
      have he : checkedAdd (fuel + 1) world [(.number left, .number left), (.number right, .number right)] = some (final, packet, cost) := hrun
      rw [h.1] at he
      obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, (h.2.2.2.2 guards).preserves⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
