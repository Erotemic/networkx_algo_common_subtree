# 14. Bibliography and evidence locators

Citation IDs are shared by the roadmap, census and machine-readable `evidence/sources.json`. An entry marked citation-chain or metadata-only is not evidence that its theorem statements or source build have been checked. Dates distinguish publication, artifact registration, code revision and retrieval. No external dependency was built during this documentation task.

## L01. Mathlib: asymptotics, finite sums, and Akra-Bazzi

**Date/revision:** Project pin v4.35.0; live docs inspected 2026-11-14. **Ecosystem:** Lean.

**Primary locator:** https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Defs.html

**Read/inspect at:** Asymptotics.IsBigOWith, IsBigO, IsTheta; Mathlib.Computability.AkraBazzi.AkraBazzi / AkraBazziRecurrence.isTheta_asympBound.

**Evidence:** official API inspected.
**Supported use:** Existing mathematical substrate, including filter-based multivariate domains and a discrete Akra-Bazzi theorem.
**Limit:** Live API docs can be newer than the project pin. Check exact declarations in the pinned checkout before writing imports; this is not an operational cost semantics.
**Disposition:** reuse.

Additional primary source: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/AkraBazzi/AkraBazzi.html

## L02. arlib: Charged and RAM realization

**Date/revision:** 8d08f89a6d05c5e8368e91659bd6e117fbb74c4e; commit 2026-10-17. **Ecosystem:** Lean.

**Primary locator:** https://github.com/meelgroup/arlib/tree/8d08f89a6d05c5e8368e91659bd6e117fbb74c4e

**Read/inspect at:** Arlib/Computation/{Charged,Cost,ExactRealization}.lean; docs/dev/Cost-Modelling-Protocol.md.

**Evidence:** selected pinned source inspected; other modules audited in repository.
**Supported use:** Typed cost vectors, data-structure contracts and exact value/opcode correspondence. ExactRealizes.bind and steps_eq already address compositional realization.
**Limit:** Own RAM model; not automatic Aeneas/Rust or physical-memory adequacy. No integration build executed here.
**Disposition:** mandatory pilot.

Additional primary source: https://github.com/meelgroup/arlib/blob/8d08f89a6d05c5e8368e91659bd6e117fbb74c4e/Arlib/Computation/ExactRealization.lean

## L03. CSLib TimeM and CSLib program

**Date/revision:** Live TimeM docs; CSLib preprint arXiv:2602.04846 (2026). **Ecosystem:** Lean.

**Primary locator:** https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html

**Read/inspect at:** Design Principles; TimeM.ret, TimeM.time, time_bind.

**Evidence:** official API inspected.
**Supported use:** Lightweight cost annotations and value/cost composition; a useful interchange and baseline representation.
**Limit:** Documentation explicitly makes annotation-to-execution matching a manual responsibility. A sound external realization theorem can still use this representation.
**Disposition:** adapter baseline.

Additional primary source: https://arxiv.org/abs/2602.04846

## L04. Lean Std.WP and vcgen

**Date/revision:** Lean 4.35.0 release, 2026-10-12. **Ecosystem:** Lean.

**Primary locator:** https://lean-lang.org/doc/reference/latest/releases/v4.35.0/

**Read/inspect at:** Highlights: vcgen; reference chapter The vcgen tactic; Std.WP.WP, @[spec].

**Evidence:** official release and reference inspected.
**Supported use:** Generalized weakest-precondition interface and proof-producing verification conditions, including deep embeddings and general assertion lattices.
**Limit:** Experimental. Does not choose or certify an execution-cost semantics on its own. Test exact pinned API and supported assertions.
**Disposition:** reuse before new VCG.

Additional primary source: https://lean-lang.org/doc/reference/latest/The--vcgen--tactic/

Additional primary source: https://lean-lang.org/doc/tutorials/latest/vcgen/

## L05. A Refinement Framework for the Word RAM (lax-62)

**Date/revision:** Registered 2026-09-02; source 0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e. **Ecosystem:** Lean.

**Primary locator:** https://laxarchive.org/lax-62/index.html

**Read/inspect at:** refinement-tower/proofs/Lax62Proofs.lean; Refine/NREST/Basic.lean; Refine/Codegen/Examples/EndToEnd.lean lines 1-140.

**Evidence:** registry and selected pinned source inspected.
**Supported use:** Lean NREST, timed/data refinement, separation/refinement machinery, structured IR and Word RAM cost path; substantial overlap with a proposed general stack.
**Limit:** No build or complete axiom audit here. Example source says independent fcCount/filter and rvOutFn/reverse functional specifications remain a backlog item. Registry status is not review acceptance.
**Disposition:** mandatory competing pilot.

Additional primary source: https://github.com/lax-archive/lax-submissions/tree/0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e/refinement-tower

## L06. Iris in Lean and iris-lean

**Date/revision:** de Medeiros et al.; arXiv:2609.24252, 2026-09-21. **Ecosystem:** Lean.

**Primary locator:** https://arxiv.org/abs/2609.24252

**Read/inspect at:** Introduction and implementation discussion; leanprover-community/iris-lean.

**Evidence:** paper text and official project discovery inspected.
**Supported use:** Existing separation-logic substrate, proof mode and Mathlib integration; candidate for resource ownership and shared-work reasoning.
**Limit:** Do not infer that Rocq Tachis, Parcas, debit or heap-space layers are ported from the existence of Iris. Current dependency build and coverage remain to audit.
**Disposition:** ownership pilot if needed.

Additional primary source: https://github.com/leanprover-community/iris-lean

Additional primary source: https://leanprover-community.github.io/iris-lean/

## L07. Aeneas: Rust functional verification

**Date/revision:** Local pin 5a392f4b80a4d0d05abc240eb2a7fa70622a9a35; 2026 source baseline. **Ecosystem:** Lean / Rust.

**Primary locator:** https://github.com/AeneasVerif/aeneas

**Read/inspect at:** Local proofs/VERIFICATION.md; dev/regenerate_rust_lean.sh; generated modules.

**Evidence:** local configuration and verification boundary inspected.
**Supported use:** Maintained route to source-level functional statements; source instrumentation should cooperate with it.
**Limit:** No general Rust execution-cost preservation theorem was established by this audit. Translation and primitive models are explicit trust boundaries.
**Disposition:** preserve and extend narrowly.

Additional primary source: https://www.microsoft.com/en-us/research/publication/scaling-verification-of-cryptographic-software-with-aeneas-rust-and-lean/

## L08. CLRS-Lean

**Date/revision:** 9352a92ba9b1d44ad1349f9e57ac31c858ec81b8; local audit 2026-11-14. **Ecosystem:** Lean.

**Primary locator:** https://github.com/TankTechnology/CLRS-Lean/tree/9352a92ba9b1d44ad1349f9e57ac31c858ec81b8

**Read/inspect at:** FourthEdition/Chapter_25; hungarian_constructs_optimal; local reuse audit.

**Evidence:** repository audit, not freshly built here.
**Supported use:** Hungarian correctness and algorithm-analysis proof examples.
**Limit:** Balanced complete assignment existence/correctness does not supply our signed partial matching, deletion-family runtime, or actual Rust costs. Different Lean pin.
**Disposition:** reference, narrow theorem reuse.

## L09. Lean4CStheory-Library

**Date/revision:** 7f0a215d60c83906e15cbc753f7dc7e7a5d3f935; local audit 2026-11-14. **Ecosystem:** Lean.

**Primary locator:** https://github.com/Lean4CStheory/Lean4CStheory-Library/tree/7f0a215d60c83906e15cbc753f7dc7e7a5d3f935

**Read/inspect at:** Time/Basic.lean; Asymptotics/MasterTheorem/NatRecurrences.lean.

**Evidence:** repository audit.
**Supported use:** Concrete recurrence-analysis examples and a TimeM wrapper.
**Limit:** No independently inspected source adequacy theorem; different Lean pin. Recurrence solvers do not discharge degree-dependent matching sums.
**Disposition:** reference.

## L10. Tau Ceti roadmap standards

**Date/revision:** Current guidance read 2026-11-14. **Ecosystem:** Lean / roadmap.

**Primary locator:** https://taucetiproject.org/contribute/write-roadmap.html

**Read/inspect at:** TauCetiRoadmap README and CONTRIBUTING: layered APIs, sources, false neighbors, Suggested.lean.

**Evidence:** official guidance inspected.
**Supported use:** Defines the submission-quality standard: existing interfaces, checked statements, human review and coordinated scope.
**Limit:** A local campaign with experiments is not yet a timeless accepted roadmap. Software semantics is not automatically excluded by the inspected policy.
**Disposition:** packaging standard.

Additional primary source: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/README.md

Additional primary source: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/CONTRIBUTING.md

## L11. VCV-io / VCVio

**Date/revision:** Live public repository and package discovery, 2026-11-14. **Ecosystem:** Lean.

**Primary locator:** https://github.com/XC0R/VCV-io

**Read/inspect at:** README: goals and computational complexity disclaimer; Reservoir discovery of Verified-zkEVM/VCVio.

**Evidence:** public project description inspected.
**Supported use:** Oracle computations and probability foundations are adjacent to a future probabilistic-cost adapter.
**Limit:** The inspected README explicitly says computational complexity is not considered. Project identity/version changed in surfaced package results; resolve exact current source before importing.
**Disposition:** adjacent, not cost backend.

Additional primary source: https://reservoir.lean-lang.org/%40Verified-zkEVM/VCVio

## L12. The Word RAM (lax-13)

**Date/revision:** Current registry inspected 2026-11-14. **Ecosystem:** Lean.

**Primary locator:** https://laxarchive.org/lax-13/index.html

**Read/inspect at:** Lax13.Ram; RamComputes; word-length and uniform-program conventions.

**Evidence:** registry/documentation inspected.
**Supported use:** Machine model and uniformity reference for lax-62.
**Limit:** Own abstract machine; not Rust hardware semantics. Verify word-size quantifier order and encodings before transferring asymptotics.
**Disposition:** machine-model reference.

## L13. Tex2Lean

**Date/revision:** Public guide inspected 2026-11-14. **Ecosystem:** Lean workflow.

**Primary locator:** https://www.tex2lean.com/

**Read/inspect at:** Guide: time complexity with Charged; Model/Interface/Analysis separation.

**Evidence:** official guide inspected.
**Supported use:** Workflow and cost-model review patterns; points to arlib.
**Limit:** Tool guidance is not a theorem library or evidence that source costs were proved for this repository.
**Disposition:** borrow process only.

## R01. A Fistful of Dollars: Formalizing Asymptotic Complexity Claims via Deductive Program Verification

**Date/revision:** Gueneau, Chargueraud, Pottier; ESOP 2018; DOI 10.1007/978-3-319-89884-1_19. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://chargueraud.org/research/2018/bigo_credits/bigo_credits.pdf

**Read/inspect at:** Sections 3-5, especially specO and cost-function synthesis; author version pp. 13-21.

**Evidence:** primary full text parsed; screenshot retrieval failed.
**Supported use:** Modular asymptotic specifications, multivariate filters, nonnegative/monotone cost envelopes and cost-synthesis proof methodology.
**Limit:** Not a WCET result; not fully automatic. Its 2018 account of unavailable recurrence theorems is historical, not current Lean evidence.
**Disposition:** architectural reference.

## R02. Verifying the Correctness and Amortized Complexity of a Union-Find Implementation in Separation Logic with Time Credits

**Date/revision:** Chargueraud and Pottier; JAR 62(3), 331-365, 2019; online 2017; DOI 10.1007/s10817-017-9431-7. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://doi.org/10.1007/s10817-017-9431-7

**Read/inspect at:** Journal paper; authors publication catalogue; predecessor ITP 2015.

**Evidence:** primary bibliographic and author descriptions inspected.
**Supported use:** Demanding precedent for linking mathematical amortized analysis to an imperative implementation.
**Limit:** Not a generic ready-made Lean API, nor a matching deletion-family theorem.
**Disposition:** case-study reference.

Additional primary source: https://toccata.gitlabpages.inria.fr/toccata/publications/chargueraud.fr.html

## R03. Formal Proof and Analysis of an Incremental Cycle Detection Algorithm

**Date/revision:** Gueneau, Jourdan, Chargueraud, Pottier; ITP 2019; DOI 10.4230/LIPIcs.ITP.2019.18. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.18

**Read/inspect at:** Abstract and publication metadata; paper and artifact linked there.

**Evidence:** publisher/author descriptions inspected.
**Supported use:** Nontrivial amortized graph algorithm verified with time credits; useful comparison for batched matching.
**Limit:** A 2019 verification case study, not a claim that this is the fastest cycle algorithm in 2026.
**Disposition:** study charging decomposition.

## R04. Time Credits and Time Receipts in Iris

**Date/revision:** Mevel, Jourdan, Pottier; ESOP 2019; DOI 10.1007/978-3-030-17184-1_1. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://link.springer.com/chapter/10.1007/978-3-030-17184-1_1

**Read/inspect at:** Publisher record; official Iris publication list.

**Evidence:** primary record identified.
**Supported use:** Reusable separation-logic resource reasoning and distinction between upper-budget credits and recorded-time receipts.
**Limit:** Exact porting status and source theorem signatures were not audited.
**Disposition:** resource-logic reference.

## R05. Thunks and Debits in Separation Logic with Time Credits

**Date/revision:** Pottier, Gueneau, Jourdan, Mevel; POPL 2024, article 50; DOI 10.1145/3632892. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://iris-project.org/pdfs/2024-popl-pottier-gueneau-jourdan-mevel-thunks-debits.pdf

**Read/inspect at:** Abstract, introduction and logical treatment of future thunks/debits; artifact linked by Iris.

**Evidence:** primary PDF parsed and first page visually inspected.
**Supported use:** Sound reusable shared-thunk and debit reasoning; important for persistent branching rather than merely sequential telescoping.
**Limit:** Does not automatically justify sharing arbitrary matching state or cloning stored potential. Requires the actual ownership/debit rules.
**Disposition:** mandatory shared-work reading.

## R06. Tachis: Higher-Order Separation Logic with Credits for Expected Costs

**Date/revision:** Haselwarter et al.; OOPSLA 2024; DOI 10.1145/3689753; arXiv:2405.20083. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://arxiv.org/abs/2405.20083

**Read/inspect at:** Abstract; Clutch project publication/artifact links.

**Evidence:** primary project and abstract inspected.
**Supported use:** Expected-cost credit semantics for probabilistic programs.
**Limit:** Expected bounds require randomness/adversary and integrability/termination conditions appropriate to the theorem. Not implied by unit-cost dictionary operations.
**Disposition:** future expected-cost adapter.

Additional primary source: https://clutch-project.org/

## R07. An Iris for Expected Cost Analysis (ExpIris)

**Date/revision:** Lohse and Garg; arXiv:2406.00884, 2024. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://arxiv.org/abs/2406.00884

**Read/inspect at:** Abstract.

**Evidence:** primary abstract identified.
**Supported use:** Independent expected-cost logic to compare before inventing one.
**Limit:** No source/theorem-level audit in this campaign preparation.
**Disposition:** probabilistic census coverage.

## R08. The Memorist Tale: Every Thunk Every Cost All At Once

**Date/revision:** Xing Li, Yao Li, Peter Schachte, Christine Rizkallah; ESOP 2026; DOI 10.1007/978-3-032-22720-1_17. **Ecosystem:** Rocq.

**Primary locator:** https://link.springer.com/chapter/10.1007/978-3-032-22720-1_17

**Read/inspect at:** Abstract and soundness discussion; artifact 18168559.

**Evidence:** publisher full text and artifact metadata inspected.
**Supported use:** Deterministic cost/usage semantics for shared lazy computations, proved sound relative to Clairvoyance.
**Limit:** Total typed language with structural recursion and no first-class functions. Not a drop-in strict memoized Rust evaluator.
**Disposition:** sharing-semantics reference.

Additional primary source: https://zenodo.org/records/18168559

## R09. A Separation Logic for Parallel Time Complexity with Work and Span Credits (Parcas)

**Date/revision:** Moine, Westrick, Tassarotti; 2026; arXiv:2607.11582; DOI 10.1145/3828679. **Ecosystem:** Rocq.

**Primary locator:** https://arxiv.org/abs/2607.11582

**Read/inspect at:** Abstract; author text; artifact 20432258.

**Evidence:** primary text and artifact metadata inspected.
**Supported use:** Work and span have different composition; task-tagged span credits handle fork/join.
**Limit:** Sequential work infrastructure is not automatically parallel span infrastructure. Not required for current subtree campaign core.
**Disposition:** separate future work/span track.

Additional primary source: https://zenodo.org/records/20432258

## R10. Foundational Verification of Running-Time Bounds for Interactive Programs

**Date/revision:** Tockman, Singh, Erbsen, Gruetter, Chlipala; CPP 2026, 187-200; DOI 10.1145/3779031.3779088. **Ecosystem:** Rocq.

**Primary locator:** https://dspace.mit.edu/entities/publication/fb2db054-1df8-42dc-8145-ea4bbe7adce8

**Read/inspect at:** Abstract and publication record; CPP 2026 programme.

**Evidence:** primary record inspected.
**Supported use:** End-to-end route from source time specifications through compilation to RISC-V semantics.
**Limit:** Different language/compiler path from Aeneas. Machine semantics does not provide a generic physical-time theorem for arbitrary hardware.
**Disposition:** source-cost architecture reference.

## R11. A High-Level Separation Logic for Heap Space under Garbage Collection

**Date/revision:** Moine, Chargueraud, Pottier; POPL 2023; DOI 10.1145/3571218. **Ecosystem:** Rocq / Coq.

**Primary locator:** https://popl23.sigplan.org/details/POPL-2023-popl-research-papers/25/A-High-Level-Separation-Logic-for-Heap-Space-under-Garbage-Collection

**Read/inspect at:** Conference abstract and artifact 7129302.

**Evidence:** primary metadata and abstract inspected.
**Supported use:** Space credits and reachability-aware live heap reasoning.
**Limit:** Allocation counts and mathematical value sizes are insufficient for live heap bounds; Rust ownership and allocator semantics differ.
**Disposition:** space-reference track.

Additional primary source: https://zenodo.org/records/7129302

## R12. Will It Fit? Verifying Heap Space Bounds of Concurrent Programs under Garbage Collection

**Date/revision:** Moine, Chargueraud, Pottier; TOPLAS 2025; DOI 10.1145/3716312. **Ecosystem:** Rocq.

**Primary locator:** https://doi.org/10.1145/3716312

**Read/inspect at:** Publisher and author publication records.

**Evidence:** primary record identified.
**Supported use:** Recent extension of heap-space verification to concurrent programs.
**Limit:** Full source and theorem audit not performed; not a prerequisite for deterministic DP-table residency.
**Disposition:** space census coverage.

## I01. Verified Memoization and Dynamic Programming

**Date/revision:** Wimmer, Shuwei Hu, Nipkow; ITP 2018, LNCS 10895, 579-596. **Ecosystem:** Isabelle/HOL.

**Primary locator:** https://www21.in.tum.de/~nipkow/pubs/itp18dp.html

**Read/inspect at:** Paper abstract/BibTeX; AFP Monad_Memo_DP.

**Evidence:** author page and AFP discovery inspected.
**Supported use:** Verified memoization transformations and bottom-up/space-efficient DP development.
**Limit:** Do not equate functional memoization correspondence with every resource theorem proposed here. Author PDF fetch failed during this audit.
**Disposition:** mandatory memoization reference.

Additional primary source: https://devel.isa-afp.org/entries/Monad_Memo_DP.html

## I02. Refinement with Time - Refining the Run-Time of Algorithms in Isabelle/HOL

**Date/revision:** Haslbeck and Lammich; ITP 2019; DOI 10.4230/LIPIcs.ITP.2019.20. **Ecosystem:** Isabelle/HOL.

**Primary locator:** https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.20

**Read/inspect at:** Sections 2.1-2.5: NREST, refinement, VCG and data refinement.

**Evidence:** primary PDF text and page 20:3 visually inspected.
**Supported use:** Result-dependent nondeterministic cost bounds and refinement-based derivation of algorithm costs.
**Limit:** Finite successful runs and totality must be separated from top/failure and unbounded resource specifications.
**Disposition:** mandatory semantic reference.

## I03. For a Few Dollars More: Verified Fine-Grained Algorithm Analysis Down to LLVM

**Date/revision:** Haslbeck and Lammich; ESOP 2021; TOPLAS 44(3), 2022; DOI 10.1145/3486169. **Ecosystem:** Isabelle/HOL.

**Primary locator:** https://doi.org/10.1145/3486169

**Read/inspect at:** Journal record; AFP NREST related publications; author full text.

**Evidence:** primary text parsed; screenshot retrieval failed.
**Supported use:** Fine-grained currencies and refinement to LLVM-level execution model.
**Limit:** LLVM model bound is not unspecified physical time or the Rust/Aeneas path.
**Disposition:** cost-exchange and refinement reference.

Additional primary source: https://www21.in.tum.de/~haslbema/documents/Haslbeck_Lammich_LLVM_with_Time.pdf

## I04. NREST: Nondeterministic Result Monad with Time

**Date/revision:** Haslbeck; AFP entry 2024-09-16. **Ecosystem:** Isabelle/HOL.

**Primary locator:** https://isa-afp.org/entries/NREST.html

**Read/inspect at:** NREST, DataRefinement, RefineMonadicVCG, Refine_Foreach sessions.

**Evidence:** official AFP entry inspected.
**Supported use:** Maintained formal development underlying timed refinement and the inspected Lean port.
**Limit:** Not directly importable into Lean. Code license and source version need review before copying/porting.
**Disposition:** upstream semantic source.

## I05. Amortized Complexity Verified / Amortized_Complexity

**Date/revision:** Nipkow; ITP 2015 and JAR journal version; maintained AFP entry. **Ecosystem:** Isabelle/HOL.

**Primary locator:** https://www21.in.tum.de/~nipkow/pubs/jar18.html

**Read/inspect at:** Journal paper and AFP Amortized_Complexity.

**Evidence:** author page and AFP entry inspected.
**Supported use:** Mechanized potential analyses of amortized data structures.
**Limit:** Regenerated 2026 PDF timestamp is not a new 2026 research result. Representation/source adequacy still needs its own statement.
**Disposition:** reuse proof organization.

Additional primary source: https://devel.isa-afp.org/entries/Amortized_Complexity.html

## I06. Verifying Asymptotic Time Complexity of Imperative Programs in Isabelle

**Date/revision:** Zhan and Haslbeck; IJCAR 2018; DOI 10.1007/978-3-319-94205-6_35. **Ecosystem:** Isabelle/HOL.

**Primary locator:** https://doi.org/10.1007/978-3-319-94205-6_35

**Read/inspect at:** Bibliography of timed-refinement work.

**Evidence:** citation identified, detailed inspection pending.
**Supported use:** Additional imperative/asymptotic verification methodology.
**Limit:** No theorem-specific adoption claim until the source is read.
**Disposition:** targeted follow-up before automation design.

## A01. Amortised Resource Analysis with Separation Logic

**Date/revision:** Robert Atkey; LMCS 7(2:17), 2011; DOI 10.2168/LMCS-7(2:17)2011. **Ecosystem:** Semantics / separation logic.

**Primary locator:** https://lmcs.episciences.org/685

**Read/inspect at:** Publisher abstract and paper.

**Evidence:** primary publisher record inspected.
**Supported use:** Published foundation for combining consumable resources and heap reasoning.
**Limit:** Porting a resource logic is substantive; do not cite this as a verbatim generic memoization theorem.
**Disposition:** resource-adequacy provenance.

## A02. Lightweight Semiformal Time Complexity Analysis for Purely Functional Data Structures

**Date/revision:** Nils Anders Danielsson; POPL 2008. **Ecosystem:** Agda / cost annotations.

**Primary locator:** https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html

**Read/inspect at:** Reference [Dan08] in TimeM; original citation linked there.

**Evidence:** citation chain only.
**Supported use:** Historical basis of lightweight ticked cost representations.
**Limit:** Original text not reopened in this audit; no exact theorem claim taken from it.
**Disposition:** background follow-up.

## A03. A Cost-Aware Logical Framework (calf)

**Date/revision:** Niu, Sterling, Grodin, Harper; POPL 2022; DOI 10.1145/3498670. **Ecosystem:** Agda / dependent type theory.

**Primary locator:** https://doi.org/10.1145/3498670

**Read/inspect at:** Abstract and author project page.

**Evidence:** primary publication/author descriptions inspected.
**Supported use:** Separates extensional program reasoning from intensional cost reasoning; relevant design alternative.
**Limit:** A separate cost-aware type theory is a much larger commitment than a Lean adapter.
**Disposition:** design comparison.

Additional primary source: https://www.cs.cmu.edu/~runmingl/calf.html

## A04. Decalf: A Directed, Effectful Cost-Aware Logical Framework

**Date/revision:** arXiv:2307.05938, 2023. **Ecosystem:** Type theory.

**Primary locator:** https://arxiv.org/abs/2307.05938

**Read/inspect at:** Abstract.

**Evidence:** primary abstract identified.
**Supported use:** Effectful generalization of cost-aware reasoning.
**Limit:** No claim of an importable Lean implementation or exact compatibility.
**Disposition:** boundary/reference.

## A05. Automatic amortized resource analysis: RAML and certificate-producing approaches

**Date/revision:** Literature lineage surveyed in R01 section 6; further source inspection pending. **Ecosystem:** AARA / type-based analysis.

**Primary locator:** https://chargueraud.org/research/2018/bigo_credits/bigo_credits.pdf

**Read/inspect at:** Related work: RAML and Pastis; see bibliography for primary papers.

**Evidence:** citation-chain survey, not implementation audit.
**Supported use:** Potential inference and checkable resource certificates are relevant to later automation.
**Limit:** Do not assume a particular current implementation is certified from this historical description. Resolve primary artifacts before reuse.
**Disposition:** separate inference track.

## A06. Amortized Computational Complexity

**Date/revision:** Robert E. Tarjan; SIAM Journal on Algebraic and Discrete Methods 6(2), 1985; DOI 10.1137/0606031. **Ecosystem:** Algorithms.

**Primary locator:** https://doi.org/10.1137/0606031

**Read/inspect at:** Classical survey; potential/accounting methods.

**Evidence:** bibliographic provenance; formal-method papers provide inspected mechanized treatment.
**Supported use:** Classical provenance for potential and charging analysis.
**Limit:** The generic operational API proposed here is a new packaging, not a verbatim theorem from this survey.
**Disposition:** mathematical provenance.

## A07. Purely Functional Data Structures

**Date/revision:** Chris Okasaki; book, 1998/1999 editions; cited by R05. **Ecosystem:** Algorithms / persistent data.

**Primary locator:** https://iris-project.org/pdfs/2024-popl-pottier-gueneau-jourdan-mevel-thunks-debits.pdf

**Read/inspect at:** R05 introduction and references to Okasaki; exact edition to pin before quotation.

**Evidence:** citation chain; R05 checked.
**Supported use:** Persistent amortization and lazy debits are relevant to branching reuse.
**Limit:** Do not use a sequential potential proof to justify persistence. Original book was not directly inspected here.
**Disposition:** provenance/background.

## P01. Lozano-Valiente common-subtree paper

**Date/revision:** 2004; source pin in local paper_statement_crosswalk.md. **Ecosystem:** Target algorithm.

**Primary locator:** https://www.cs.upc.edu/~antoni/subtree.pdf

**Read/inspect at:** Theorem 3 and decomposition/state bounds; local containment audit.

**Evidence:** repository crosswalk and corresponding Lean code inspected.
**Supported use:** First real client: state count, memo requests and representation-aware cost.
**Limit:** Printed containment issue and corrected leaf/depth conventions must remain visible. Original PDF hash is repository-reported.
**Disposition:** local client.

## P02. Droschinsky-Kriege-Mutzel common subtree isomorphism paper

**Date/revision:** 2016; arXiv:1602.07210v4. **Ecosystem:** Target algorithm.

**Primary locator:** https://arxiv.org/abs/1602.07210v4

**Read/inspect at:** Lemmas 5/6 and Theorems 4/7 in local crosswalk.

**Evidence:** repository crosswalk and matching source context inspected.
**Supported use:** Rectangular matching and related deletion-family costs drive batch contracts.
**Limit:** Optimized runtime does not follow from existence/correctness of a matching; exact paper-side assumptions must be restated.
**Disposition:** local client.

## P03. Droschinsky-Kriege-Mutzel largest weight common subtree embeddings

**Date/revision:** 2018; arXiv:1805.00821v1. **Ecosystem:** Target algorithm.

**Primary locator:** https://arxiv.org/abs/1805.00821v1

**Read/inspect at:** Original HTML sections 4-5, especially section 5.2 Lemmas 12-14 and Theorem 15; local crosswalk.

**Evidence:** original paper HTML and repository proof boundary inspected.
**Supported use:** Oriented DP scheduling, shared maxima, matching families and table space.
**Limit:** Unrooted structural obligations and integer-weight space qualifications remain; source tests are not formal resource proofs.
**Disposition:** local client.

Additional primary source: https://arxiv.org/html/1805.00821v1

## L14. Order Maintenance in Worst-Case Constant Time, Verified

**Date/revision:** Denis Firsov; arXiv:2610.38616v1, 2026-10-28. **Ecosystem:** Lean.

**Primary locator:** https://arxiv.org/html/2610.38616v1

**Read/inspect at:** Sections 4.1-4.6 and appendix C; README points to OM/Impl/{TheoremsM,PeakRun,PeakWord,FlatRun}.lean.

**Evidence:** primary paper text and repository README inspected; README blob 5a98944785cb2b4f6781ba0a8251252926d6d4fc.
**Supported use:** Recent execution-linked cost and word-size development with step-preserving translation. Important semantic/refinement reuse candidate.
**Limit:** No build or theorem-source audit here. Paper RAM includes unit-cost zero-filled allocation; current README also reports a flat-memory translation. Neither establishes cost adequacy for our Rust source; Rust transpilation is checked by tests in the reported workflow.
**Disposition:** mandatory targeted source audit, not automatic dependency.

Additional primary source: https://github.com/dfirsov/order_maintenance

## L15. complexity-lean: model-parametric complexity classes

**Date/revision:** Public README inspected 2026-11-14; reported Lean/Mathlib 4.32.2. **Ecosystem:** Lean.

**Primary locator:** https://github.com/alonamaloh/complexity-lean

**Read/inspect at:** Complexity/Model; Models/While, Models/Fun, Models/Shallow and Models/PartrecCost; README blob cd063842829eaaa17adc3ff217299eaa7fd9bae8.

**Evidence:** project README inspected, not declaration/build audit.
**Supported use:** Model composition and explicit cost boundaries; fuel need not equal work. Offers a separate complexity-class use case.
**Limit:** Its shallow-model impossibility concerns encoding all functions as countable program syntax, not impossibility of proving bounds for particular shallow programs. README carries ReductionsComputable explicitly and does not prove model invariance to Turing machines.
**Disposition:** inspect model contracts; adjacent scope.

## L16. Verified Dynamic Programming with Sigma-types in Lean

**Date/revision:** Tanner Duve, 2025-05-21. **Ecosystem:** Lean.

**Primary locator:** https://tannerduve.github.io/blog/2025/verified-dp/

**Read/inspect at:** Independent recurrence and memo table carrying correctness witnesses.

**Evidence:** author tutorial and code text inspected.
**Supported use:** Existing Lean memo correctness pattern; avoid treating basic cache soundness as absent.
**Limit:** Tutorial is not a generic source-runtime resource theorem. HashMap use does not establish its cost. No build reproduced.
**Disposition:** correctness-interface reference.

## L17. Agentic Verified Optimization of Real-World Software

**Date/revision:** Ye, Ghai, Qin, Song and Kong; arXiv:2610.30188, 2026-10-20. **Ecosystem:** Lean.

**Primary locator:** https://arxiv.org/abs/2610.30188

**Read/inspect at:** Abstract and introduction: proved equivalence and benchmarked performance; Aqueduct migration boundary.

**Evidence:** primary text inspected.
**Supported use:** Recent adjacent optimization work illustrates functional equivalence plus empirical improvement.
**Limit:** Do not count measured speedups as formal asymptotic bounds, or differentially tested source ports as source-cost refinement.
**Disposition:** related but not a cost-theorem backend.

## R13. CertiRocq / CertiCoq compilation and space-safety work

**Date/revision:** Official status inspected 2026-11-14; Closure Conversion is Safe for Space, ICFP 2019; compiler experience report August 2026. **Ecosystem:** Rocq.

**Primary locator:** https://certicoq.org/

**Read/inspect at:** Official overview, verification status and publications; space paper DOI 10.1145/3341687.

**Evidence:** official project overview and publication record inspected.
**Supported use:** Compiler-stage resource preservation is an established separate research concern.
**Limit:** Project says some compiler components remain under verification. Functional compiler correctness alone is not arbitrary time/space preservation; exact resource theorem and formalized scope require audit.
**Disposition:** compiler/space reference, outside first core.

Additional primary source: https://doi.org/10.1145/3341687

## R14. A Certifying Extraction with Time Bounds from Coq to Call-By-Value Lambda Calculus

**Date/revision:** Yannick Forster and Fabian Kunze; ITP 2019, article 17. **Ecosystem:** Rocq.

**Primary locator:** https://doi.org/10.4230/LIPIcs.ITP.2019.17

**Read/inspect at:** Author/publisher abstract; logical relation relating Coq functions, extracted terms and time bounds; linked artifact.

**Evidence:** primary author and publisher records inspected.
**Supported use:** Direct precedent for certifying translation and automatic time-bound validation, complementing CFML.
**Limit:** Exact supported source fragment, logical-relation statement and automation limitations must be read before porting. This is not a Rust execution theorem.
**Disposition:** mandatory source-bridge design reading.

Additional primary source: https://www.ps.uni-saarland.de/Publications/details/ForsterKunze%3A2019%3ACertifying-extraction.html

Additional primary source: https://github.com/uds-psl/certifying-extraction-with-time-bounds

## R15. The Weak Call-By-Value Lambda-Calculus is Reasonable for Both Time and Space

**Date/revision:** Forster, Kunze and Roth; POPL 2020; arXiv:1902.07515. **Ecosystem:** Rocq / complexity theory.

**Primary locator:** https://ps.uni-saarland.de/extras/wcbv-reasonable/

**Read/inspect at:** Author project and linked mechanized portions; artifact DOI 10.1145/3373103.

**Evidence:** author record and artifact description inspected.
**Supported use:** Explains model invariance and the relationship between reduction counts, term space and machine complexity.
**Limit:** Artifact identifies formalized portions, not a blanket certification of every paper argument. Reasonable polynomial overhead is weaker than preserving a tight target bound.
**Disposition:** model-boundary reference.

Additional primary source: https://doi.org/10.1145/3373103

Additional primary source: https://github.com/uds-psl/cbv-lambda-calculus-reasonable

## R16. Mechanising Complexity Theory: The Cook-Levin Theorem in Coq

**Date/revision:** Lennard Gaher and Fabian Kunze; ITP 2021, article 20. **Ecosystem:** Rocq.

**Primary locator:** https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.20

**Read/inspect at:** Publisher record; author artifact linked through uds-psl/cook-levin.

**Evidence:** primary publication and artifact records inspected.
**Supported use:** A substantial use of compositional computation/time infrastructure for complexity-theory proofs.
**Limit:** Different client than tight RAM data-structure analysis. Artifact/build and current Rocq compatibility not audited here.
**Disposition:** independent reuse and extraction reference.

Additional primary source: https://uds-psl.github.io/cook-levin/

## A08. AutoCLRS / AlgoStar in F* and Pulse

**Date/revision:** RiSE MSR author report, 2026-03-06; later specification-audit reports in 2026. **Ecosystem:** F* / Pulse.

**Primary locator:** https://risemsr.github.io/blog/2026-03-06-autoclrs/

**Read/inspect at:** Algorithm/complexity examples and discussion of specification audit; official AlgoStar repository.

**Evidence:** primary author report inspected.
**Supported use:** Adjacent imperative algorithm-verification campaign; examples of linked counting and explicit specification-review failures.
**Limit:** Per-algorithm hypotheses and count linkage differ. Do not transfer a ghost counter to machine cost without adequacy, or generalize a successful build to the intended specification.
**Disposition:** comparative methodology and review reference.

Additional primary source: https://github.com/FStarLang/AlgoStar

Additional primary source: https://risemsr.github.io/blog/2026-04-16-spotting-specs/
