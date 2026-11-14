# 02. Related-work census and comparative assessment

## 1. Evidence standard

This is a coverage-oriented census as of **2026-11-14**, not a ranking of prover ecosystems and not a certification of third-party packages. The bibliography and JSON identify precisely what was inspected. Use these evidence classes:

* **Selected source/API:** actual declarations or official API documentation inspected, with a revision when available. This does not imply a successful build or whole-library axiom review.
* **Primary text:** paper text or author description inspected. This establishes the published claim, not porting status or reproducibility here.
* **Primary record:** publisher/author abstract, artifact metadata or official archive entry inspected. Exact theorem numbers and hypotheses remain to be checked before a formal port.
* **Repository audit:** a prior, explicit source audit included in the uploaded repository. Its pin and limitations are inherited, not relabeled as fresh execution.
* **Citation chain:** identified through a checked source but not itself inspected deeply. These are named research debts, not adoption evidence.

A search miss never establishes global absence. A library name, public badge, word "verified," or private constructor never replaces a theorem-signature audit.

## 2. Findings that change the initial campaign proposal

### Existing Lean infrastructure is broader than a simple cost monad

[L02] has explicit realization composition. [L05] contains a broad timed refinement and code-generation stack. [L04] supplies a generalized proof automation frontend on the repository's current Lean release. [L06] supplies a potential ownership substrate. The campaign must begin with reuse experiments instead of treating these layers as wholly absent.

### Rocq's relevant lead is a collection of sound methods

The comparison should be capability-specific. [R01--R03] demonstrate modular amortized and asymptotic implementation verification. [R05] addresses persistent shared computation through thunks and debits. [R06--R07] address expected cost. [R08] gives a 2026 deterministic semantics for a restricted lazy language. [R09] gives 2026 work/span resource reasoning. [R10] gives a 2026 source-to-RISC-V time-bound path. These are different semantics and cannot be combined by importing a generic "cost" type.

### Certifying extraction is an additional Rocq branch

[R14] supplies a published certifying extraction/time-bound approach; [R15--R16] connect that line to computational models and complexity theory. These are mandatory references for the source-bridge design, alongside CFML. [R13] records the distinct compiler/space-preservation boundary. None implies preservation of a tight Rust RAM bound without the relevant simulation.

### Isabelle is a direct architectural reference

[I01] addresses memoization correctness; [I02--I04] address timed refinement, currencies and imperative execution; [I05] addresses amortized analyses. The new Lean Lax62 source explicitly identifies the Isabelle NREST lineage. Before porting Isabelle concepts anew, inspect the existing Lean adaptation and its remaining proof boundaries.

## 3. Capability matrix

`Yes` means the cited inspected material supports that capability in its own setting. `Boundary` means extra semantics or a bridge is required. `Not audited` is not a negative claim.

| Family | Costed execution/adequacy | Modular amortization | Memo/shared evaluation | Asymptotic interface | Source/machine endpoint |
|---|---|---|---|---|---|
| Mathlib [L01] | Boundary | Mathematical ingredients | Finite combinatorics | Yes | None supplied by these modules |
| arlib [L02] | Own charged/RAM correspondence | Relevant resource contracts; exact coverage to test | Primitives available; generic DP theorem not identified | Mathlib-compatible candidate | Own RAM examples, not our Rust |
| CSLib TimeM [L03] | Trusted annotations until bridged | Can carry costs; no automatic adequacy | Client supplied | Other libraries can wrap it | Boundary |
| Lean `Std.WP` [L04] | Requires a WP interpretation and its soundness | Assertion-lattice support | Client/backend supplied | Client supplied | Backend-defined |
| Lax62 [L05] | Timed refinement and machine path in source | Amortization modules present | Generic demanded memo theorem not identified | Modules present | Own Word RAM; selected examples sampled |
| Iris-Lean [L06] | General logical substrate | Ownership foundation | Specific credits/debits layer not audited | Mathlib integration | Language-dependent |
| CFML [R01--R03] | Yes in defined language/model | Yes | Concrete case studies | Yes | Verified source-program specifications |
| Iris credits/debits [R04--R05] | Yes in their formal models | Yes | Shared thunks/debits | Client specifications | Language-model boundary |
| Tachis/ExpIris [R06--R07] | Expected-cost semantics | Expected credits | Not general strict memoization | Model-dependent | Probabilistic language model |
| Memorist [R08] | Soundness to a lazy semantics | Scope-specific | Yes for restricted lazy language | Not the main interface | No Rust correspondence |
| Parcas [R09] | Work/span adequacy | Parallel credit rules | Fork/join sharing discipline | Work/span specs | Abstract parallel semantics |
| Isabelle NREST [I02--I04] | Yes | Timed/resource refinement | Requires DP adapter | Yes | LLVM-level model in extended work |
| calf/decalf [A03--A04] | Cost-aware theory | Cost reasoning supported | Setting-dependent | Theory-dependent | Not a Lean/Rust adapter |
| Order-maintenance Lean [L14] | Deep RAM and reported exact translation | Specific worst-case analysis | Not the focus | Exact work/value-size bounds | Defined machine; Rust conformance tests |
| Certifying extraction [R14--R16] | Extracted lambda-calculus time semantics | Different methodology | Source-fragment dependent | Time-bound/computability contracts | Certified extraction; model scope explicit |

## 4. Recent-source checks that must precede new foundations

**Lax62: audit rather than accept or dismiss.** The current registered page links `0503df0e...`, Lean 4.33 epoch. Search snippets showed an older pin; the live link was used. The root imports NREST, Sepref, cost, codegen, data interfaces and asymptotics. `NREST/Basic.lean` explicitly ports the source result-map and refinement construction. `Codegen/Examples/EndToEnd.lean` describes actual codegen cost reasoning, but says the independent specifications of the example twins are outside that example's proved scope. This is evidence for reuse and for an independent-specification gate. It is not evidence that the entire stack is unsound.

**Lean 4.35 automation:** the new name is `vcgen`, with `Std.WP`; older `mvcgen` examples alone are an incomplete account of the baseline. Prototype a cost-aware WP interpretation before considering custom proof automation. Experimental status means pinning and regression tests are necessary, not that it should be ignored.

**Iris-Lean:** the 2026 preprint makes a broad port visible. Map exactly which resource algebras, adequacy theorems, languages and proof-mode features are available. Do not infer cost-specific port completion from the core logic. A short linear batch ledger may avoid a large dependency until shared mutable state requires it.

**October 2026 order-maintenance development:** [L14] reports a deep RAM, a step-preserving translation and value-size bounds. Inspect its semantics and reusable translation lemmas before designing a source/cost layer. Its allocation convention is explicit; the current README additionally reports a flat-memory version. The paper and README were inspected, not the full proof build.

**Other adjacent work:** [L15] concerns explicit computation models for complexity classes; [L16] already demonstrates a Lean memo-correctness pattern; [L17] proves equivalence while measuring speedups. They should not be conflated with a generic tight runtime proof library. [A08] provides another 2026 algorithm-formalization campaign and specification-audit experience.

## 5. Census decisions by family

### Use directly or with a thin adapter

[L01] supplies mathematical language. [L02], [L04] and [L05] are mandatory alternatives in the initial backend experiment. [L07] stays the existing source-correctness boundary. Use [L03] as an intentionally lightweight baseline to expose how much additional adequacy evidence a particular backend supplies.

### Study for design and port only a demonstrated gap

[R01], [R05], [R14], [I01--I04] are the mandatory reading set; [L14] is a mandatory targeted source audit. Their roles differ: specification abstraction, ownership/sharing, memoization and cost refinement. [R02--R03] and [I05] are demanding proof-organization case studies. [L06] becomes a direct candidate when a contract truly needs separation ownership. [A01] supplies resource-logic provenance.

### Keep visible, outside the first committed core

Expected hashing [R06--R07], lazy semantics [R08], parallel span [R09], GC/concurrent heap bounds [R11--R12], dependent cost theories [A03--A04], and automated potential inference [A05] are separate research tracks. Their existence constrains interface design, but does not justify importing all their machinery into a sequential deterministic DP pilot.

### Do not treat as a missing runtime library

[L08] already overlaps matching correctness. [L09] offers recurrence examples rather than our missing family-accounting connection. [L11] is adjacent probability/oracle work, not an audited execution-cost backend. [L13] is formalization workflow guidance. None justifies redoing established local correctness developments.

## 6. Exact-source handoff policy

Before adopting a published result, extend its record with the exact version, theorem/section, original hypotheses, representation choices, proposed Lean signature, source-code declaration and all nonstandard axioms. Before adopting code, add its commit, license, toolchain, imports, build command and independently reviewed consumer. A theorem's source locator must survive a future website redesign: keep DOI/arXiv version or commit alongside the human-readable URL.

Not every item in this census has reached that level. The evidence field says which have. In particular, the generic event, memo and batch theorems proposed below are **campaign formulations assembled from established ideas**. They must not be advertised as verbatim ports of unnamed results from these papers.

## 7. Coverage limits

The search included Lean/Mathlib/CSLib, arlib, Aeneas, Tau Ceti, Lax, Iris, CFML, Rocq expected/shared/parallel/space work, Isabelle AFP/timed refinement, certifying extraction, model invariance, CertiRocq, F*/Pulse and cost-aware type-theoretic alternatives. Recent 2026 sources were explicitly sought. Private discussions, every open PR, unreleased branches, and every current artifact build were not exhaustively checked. See [search-log.md](evidence/search-log.md) for the refresh procedure. A public coordination query to maintainers is a required pre-implementation step, not work claimed to have happened here.

## 8. Per-source index

The following index is generated from the same source records as the bibliography. It is an inventory, not a substitute for the evidence and limitations in [14](14-bibliography.md).

| ID | Work / family | Evidence | Disposition |
|---|---|---|---|
| [L01](14-bibliography.md) | Mathlib: asymptotics, finite sums, and Akra-Bazzi | official API inspected | reuse |
| [L02](14-bibliography.md) | arlib: Charged and RAM realization | selected pinned source inspected; other modules audited in repository | mandatory pilot |
| [L03](14-bibliography.md) | CSLib TimeM and CSLib program | official API inspected | adapter baseline |
| [L04](14-bibliography.md) | Lean Std.WP and vcgen | official release and reference inspected | reuse before new VCG |
| [L05](14-bibliography.md) | A Refinement Framework for the Word RAM (lax-62) | registry and selected pinned source inspected | mandatory competing pilot |
| [L06](14-bibliography.md) | Iris in Lean and iris-lean | paper text and official project discovery inspected | ownership pilot if needed |
| [L07](14-bibliography.md) | Aeneas: Rust functional verification | local configuration and verification boundary inspected | preserve and extend narrowly |
| [L08](14-bibliography.md) | CLRS-Lean | repository audit, not freshly built here | reference, narrow theorem reuse |
| [L09](14-bibliography.md) | Lean4CStheory-Library | repository audit | reference |
| [L10](14-bibliography.md) | Tau Ceti roadmap standards | official guidance inspected | packaging standard |
| [L11](14-bibliography.md) | VCV-io / VCVio | public project description inspected | adjacent, not cost backend |
| [L12](14-bibliography.md) | The Word RAM (lax-13) | registry/documentation inspected | machine-model reference |
| [L13](14-bibliography.md) | Tex2Lean | official guide inspected | borrow process only |
| [R01](14-bibliography.md) | A Fistful of Dollars: Formalizing Asymptotic Complexity Claims via Deductive Program Verification | primary full text parsed; screenshot retrieval failed | architectural reference |
| [R02](14-bibliography.md) | Verifying the Correctness and Amortized Complexity of a Union-Find Implementation in Separation Logic with Time Credits | primary bibliographic and author descriptions inspected | case-study reference |
| [R03](14-bibliography.md) | Formal Proof and Analysis of an Incremental Cycle Detection Algorithm | publisher/author descriptions inspected | study charging decomposition |
| [R04](14-bibliography.md) | Time Credits and Time Receipts in Iris | primary record identified | resource-logic reference |
| [R05](14-bibliography.md) | Thunks and Debits in Separation Logic with Time Credits | primary PDF parsed and first page visually inspected | mandatory shared-work reading |
| [R06](14-bibliography.md) | Tachis: Higher-Order Separation Logic with Credits for Expected Costs | primary project and abstract inspected | future expected-cost adapter |
| [R07](14-bibliography.md) | An Iris for Expected Cost Analysis (ExpIris) | primary abstract identified | probabilistic census coverage |
| [R08](14-bibliography.md) | The Memorist Tale: Every Thunk Every Cost All At Once | publisher full text and artifact metadata inspected | sharing-semantics reference |
| [R09](14-bibliography.md) | A Separation Logic for Parallel Time Complexity with Work and Span Credits (Parcas) | primary text and artifact metadata inspected | separate future work/span track |
| [R10](14-bibliography.md) | Foundational Verification of Running-Time Bounds for Interactive Programs | primary record inspected | source-cost architecture reference |
| [R11](14-bibliography.md) | A High-Level Separation Logic for Heap Space under Garbage Collection | primary metadata and abstract inspected | space-reference track |
| [R12](14-bibliography.md) | Will It Fit? Verifying Heap Space Bounds of Concurrent Programs under Garbage Collection | primary record identified | space census coverage |
| [I01](14-bibliography.md) | Verified Memoization and Dynamic Programming | author page and AFP discovery inspected | mandatory memoization reference |
| [I02](14-bibliography.md) | Refinement with Time - Refining the Run-Time of Algorithms in Isabelle/HOL | primary PDF text and page 20:3 visually inspected | mandatory semantic reference |
| [I03](14-bibliography.md) | For a Few Dollars More: Verified Fine-Grained Algorithm Analysis Down to LLVM | primary text parsed; screenshot retrieval failed | cost-exchange and refinement reference |
| [I04](14-bibliography.md) | NREST: Nondeterministic Result Monad with Time | official AFP entry inspected | upstream semantic source |
| [I05](14-bibliography.md) | Amortized Complexity Verified / Amortized_Complexity | author page and AFP entry inspected | reuse proof organization |
| [I06](14-bibliography.md) | Verifying Asymptotic Time Complexity of Imperative Programs in Isabelle | citation identified, detailed inspection pending | targeted follow-up before automation design |
| [A01](14-bibliography.md) | Amortised Resource Analysis with Separation Logic | primary publisher record inspected | resource-adequacy provenance |
| [A02](14-bibliography.md) | Lightweight Semiformal Time Complexity Analysis for Purely Functional Data Structures | citation chain only | background follow-up |
| [A03](14-bibliography.md) | A Cost-Aware Logical Framework (calf) | primary publication/author descriptions inspected | design comparison |
| [A04](14-bibliography.md) | Decalf: A Directed, Effectful Cost-Aware Logical Framework | primary abstract identified | boundary/reference |
| [A05](14-bibliography.md) | Automatic amortized resource analysis: RAML and certificate-producing approaches | citation-chain survey, not implementation audit | separate inference track |
| [A06](14-bibliography.md) | Amortized Computational Complexity | bibliographic provenance; formal-method papers provide inspected mechanized treatment | mathematical provenance |
| [A07](14-bibliography.md) | Purely Functional Data Structures | citation chain; R05 checked | provenance/background |
| [P01](14-bibliography.md) | Lozano-Valiente common-subtree paper | repository crosswalk and corresponding Lean code inspected | local client |
| [P02](14-bibliography.md) | Droschinsky-Kriege-Mutzel common subtree isomorphism paper | repository crosswalk and matching source context inspected | local client |
| [P03](14-bibliography.md) | Droschinsky-Kriege-Mutzel largest weight common subtree embeddings | original paper HTML and repository proof boundary inspected | local client |
| [L14](14-bibliography.md) | Order Maintenance in Worst-Case Constant Time, Verified | primary paper text and repository README inspected; README blob 5a98944785cb2b4f6781ba0a8251252926d6d4fc | mandatory targeted source audit, not automatic dependency |
| [L15](14-bibliography.md) | complexity-lean: model-parametric complexity classes | project README inspected, not declaration/build audit | inspect model contracts; adjacent scope |
| [L16](14-bibliography.md) | Verified Dynamic Programming with Sigma-types in Lean | author tutorial and code text inspected | correctness-interface reference |
| [L17](14-bibliography.md) | Agentic Verified Optimization of Real-World Software | primary text inspected | related but not a cost-theorem backend |
| [R13](14-bibliography.md) | CertiRocq / CertiCoq compilation and space-safety work | official project overview and publication record inspected | compiler/space reference, outside first core |
| [R14](14-bibliography.md) | A Certifying Extraction with Time Bounds from Coq to Call-By-Value Lambda Calculus | primary author and publisher records inspected | mandatory source-bridge design reading |
| [R15](14-bibliography.md) | The Weak Call-By-Value Lambda-Calculus is Reasonable for Both Time and Space | author record and artifact description inspected | model-boundary reference |
| [R16](14-bibliography.md) | Mechanising Complexity Theory: The Cook-Levin Theorem in Coq | primary publication and artifact records inspected | independent reuse and extraction reference |
| [A08](14-bibliography.md) | AutoCLRS / AlgoStar in F* and Pulse | primary author report inspected | comparative methodology and review reference |
