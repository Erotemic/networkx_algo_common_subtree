"""Standalone talk about Lean and Aeneas correctness evidence in this repo.

Status statements refer to proof checkpoint 267f35f (2026-11-16) and distinguish
independent mathematics, executable Lean references, translated Rust and cost.
"""
from __future__ import annotations

from manim import FadeIn, Create, Write, GrowArrow, Arrow, VGroup

from scenes import MathPresentation, MathTex
from math_examples import (node, decode_tree, encode_tree,
                           common_embedding_oracle, lozano_dp_word)
from visuals import tree_drawing, t, panel, TEAL, BLUE, AMBER, ROSE, FG, MUTED
from lecture_primitives import formula, strip, show_rows, center_text, side_formula


class F01Question(MathPresentation):
    intro_notes = ('What evidence connects a mathematical optimization '
                   'problem to an executable implementation? The repository '
                   'uses independent Lean specifications, constructive reference '
                   'algorithms, and Aeneas translation of maintained Rust source.')

    def construct(self):
        self.setup_page('Proving common-subtree computations', 'Lean 4 / Aeneas / Rust',
                        'Proof checkpoint: 267f35f / 2026-11-16; proofs/PROOF_STATUS.md')
        show_rows(self,[
            ('MATHEMATICS','define feasible common structures',TEAL,'Start with an independent finite mathematical specification.'),
            ('ALGORITHM','prove a recurrence returns the optimum',BLUE,'The executable recurrence must be both sound and complete.'),
            ('SOURCE CODE','connect real Rust entry points to contracts',AMBER,'Aeneas translates the maintained safe Rust core for source-level reasoning.'),
            ('RESOURCES','prove operation bounds separately',ROSE,'Asymptotic and allocation costs require further models and reasoning.'),
        ],start=1.43,step=1.13)
        self.finish()


class F02Feasibility(MathPresentation):
    intro_notes = ('Proof correctness needs a mathematical definition '
                   'that does not depend on the implementation being verified.')

    def construct(self):
        self.setup_page('An independent mathematical contract', 'specification versus algorithm',
                        'Paper2004/OrderedTree.lean; Shared/WeightedMatching.lean')
        left=node('r',node('a',node('b'),node('c')))
        right=node('s',node('p',node('q')))
        a,_=tree_drawing(left,anchor=(-3.6,1.84),width=3.7)
        b,_=tree_drawing(right,anchor=(3.6,1.84),width=3.7)
        self.play(Create(a),Create(b))
        self.beat(notes='The specification universally quantifies over feasible common contractions. It is not defined by the return value of the solver under test.')
        self.play(Write(formula(r'\operatorname{Common}(C,A,B)',y=-1.02,scale=1.04,color=TEAL)))
        self.beat(notes='A maximum witness is feasible and dominates the scores of all other feasible witnesses.')
        self.play(Write(formula(r'\forall D,\ \operatorname{Common}(D,A,B)\Rightarrow |E(D)|\leq |E(C)|',y=-1.90,scale=.69,color=BLUE)))
        self.beat(notes='For weighted graph problems, the same shape of theorem uses an exact score and a different feasible-mapping predicate.')
        self.play(FadeIn(center_text('The independent feasible set defines what correct means.',y=-2.73,size=22)))
        self.finish()


class F03Bridge(MathPresentation):
    intro_notes = ('The key ordered-tree bridge establishes both directions '
                   'between structural edge contraction and balanced-word '
                   'matched-pair deletion, together with encode/decode inverses.')

    def construct(self):
        self.setup_page('Prove the representation bridge', 'trees to balanced sequences',
                        'Paper2004/EncodingEquivalence.lean; ContractionCompleteness.lean')
        self.play(Write(formula(r'\operatorname{decode}(\operatorname{encode}(T))=T',y=1.64,scale=.87,color=TEAL)))
        self.beat(notes='The inverse identity ensures that the encoding does not lose the tree shape, even for branching trees.')
        self.play(Write(formula(r'\operatorname{encode}(\operatorname{decode}(w))=w',y=.55,scale=.87,color=BLUE)))
        self.beat(notes='One edge contraction corresponds to deleting a balanced matched pair in the encoding; the converse is also constructed.')
        self.play(Write(formula(r'C\preccurlyeq T\ \Longleftrightarrow\ \operatorname{enc}(C)\preccurlyeq_{\rm pair}\operatorname{enc}(T)',y=-.68,scale=.81,color=TEAL)))
        self.beat(notes='This bridge allows the recurrence proof to transfer a common balanced-word witness back to a common tree.')
        self.play(FadeIn(center_text('The representations agree on the entire feasible relation.',y=-2.19,size=22)))
        self.finish()


class F04Countermodel(MathPresentation):
    intro_notes = ('Formalization exposed a discrepancy between the '
                   'paper\'s literal printed containment relation and '
                   'arbitrary matched-pair deletion. The correction is '
                   'mathematically precise and verified in Lean.')

    def construct(self):
        self.setup_page('A proved counterexample to printed containment', 'Lozano--Valiente / Definition 2 audit',
                        'Paper2004/PrintedContainmentCounterexample.lean')
        self.play(Write(formula(r'001011\ \longrightarrow\ 0011',y=1.65,scale=1.22,color=TEAL)))
        self.beat(notes='The operational relation permits removing an inner leaf pair while preserving the enclosing root-to-child edge.')
        self.play(FadeIn(strip('OPERATIONAL','common optimum on pair (0011,001011) is 2',y=.37,accent=TEAL)))
        self.beat(notes='The literal least inductive reading of the printed clause has fewer outcomes: its optimum on this pair is only one.')
        self.play(FadeIn(strip('PRINTED','literal relation has optimum 1 on same pair',y=-.73,accent=ROSE)))
        self.beat(notes='The dynamic program is proved correct for the operational contraction relation; the discrepancy is not transferred to the algorithm.')
        self.play(FadeIn(strip('LEAN RESULT','counterexample and recurrence correctness proved',y=-1.82,accent=AMBER)))
        self.finish()


class F05ReferenceProof(MathPresentation):
    intro_notes = ('The ordered dynamic program has an independent maximum '
                   'specification, a constructive witness recurrence, and '
                   'a separate numerical memoized evaluator with state bounds.')

    def construct(self):
        self.setup_page('The correctness chain for the 2004 recurrence', 'specification to implementation',
                        'Paper2004/DynamicProgram.lean; MemoizedDynamicProgram.lean')
        show_rows(self,[
            ('WITNESS','every recursive branch constructs a feasible tree',TEAL,'Soundness: the algorithm never claims an infeasible embedding.'),
            ('COVERAGE','every feasible optimum fits one recurrence case',BLUE,'Completeness: none of the feasible optimal cases is omitted.'),
            ('VALUE','returned witness attains the global maximum',AMBER,'Soundness and completeness establish the maximum theorem.'),
            ('MEMO','cache keys are unique and confined to state product',ROSE,'The memoized evaluator is proved with explicit table-operation bounds.'),
        ],start=1.44,step=1.12)
        self.finish()


class F06RustTranslation(MathPresentation):
    intro_notes = ('Aeneas consumes generated representations of real Rust '
                   'source. A source-level theorem is stronger than checking '
                   'a hand-written Lean imitation of the intended algorithm.')

    def construct(self):
        self.setup_page('From maintained Rust to Lean theorems', 'Charon / Aeneas translation',
                        'proofs/VERIFICATION.md; Rust/Generated; Rust/OrderedSolver.lean')
        self.play(FadeIn(strip('RUST SOURCE','verified_ordered_core crate',y=1.43,accent=TEAL)))
        self.beat(notes='Charon and Aeneas produce Lean representations tied to the compiled safe Rust code. Translation pins and build steps are recorded.')
        self.play(FadeIn(strip('TRANSLATION','Charon extraction and Aeneas definitions',y=.34,accent=BLUE)))
        self.beat(notes='The proof is then stated about those actual translated definitions, under explicit numeric and representation hypotheses.')
        self.play(FadeIn(strip('LEAN RESULT','source entry point returns maximum common tree',y=-.75,accent=AMBER)))
        self.beat(notes='The checked proof covers the bounded u32 input contract. Memory allocation, runtime cost and Python wrapper behavior are outside this particular theorem.')
        self.play(FadeIn(strip('BOUNDARY','allocation, APIs and full cost models remain distinct',y=-1.83,accent=ROSE)))
        self.finish()


class F07RustMemo(MathPresentation):
    intro_notes = ('The source-level memoized ordered solver is also '
                   'verified. The proof connects its real cache to the '
                   'proved numerical dynamic-program state table.')

    def construct(self):
        self.setup_page('Memoized Rust has a source-level proof', 'ordered solver / u32-bound inputs',
                        'Rust/MemoizedOrderedSolver.lean')
        self.play(Write(formula(r'|E(\operatorname{RustMemo}(A,B))|=\operatorname{OPT}(A,B)',y=1.65,scale=.82,color=TEAL)))
        self.beat(notes='The returned structural witness and its score refine the independent optimum under the input edge-count bounds.')
        self.play(FadeIn(strip('CACHE INVARIANT','each stored pair has its verified optimum',y=.39,accent=BLUE)))
        self.beat(notes='The cache uniqueness and state-bound theorems apply to the actual translated memo entry point.')
        self.play(FadeIn(strip('MODEL COUNTS','table growth; memo-model key comparisons',y=-.72,accent=TEAL)))
        self.beat(notes='The actual data structure is an association list. LookupEvents additionally proves structural packet bounds and value erasure. Its source-event adequacy is still open; these model counts do not establish actual Rust runtime.')
        self.play(FadeIn(strip('NOT YET','source-cost adequacy and full runtime bound',y=-1.83,accent=ROSE)))
        self.finish()


class F08Assignment(MathPresentation):
    intro_notes = ('For unordered weighted common subtrees, matching '
                   'correctness is a reusable foundation. There is an '
                   'independent partial-matching optimum and actual Rust '
                   'exact-integer assignment proof.')

    def construct(self):
        self.setup_page('Verifying the weighted matching primitive', 'signed integer core / partial matching',
                        'Rust/AssignmentEntrypoint.lean; Rust/MatchingEntrypoint.lean')
        self.play(Write(formula(r'\max_{M\ \mathrm{partial}}\sum_{(i,j)\in M}w_{ij}',y=1.65,scale=1.03,color=TEAL)))
        self.beat(notes='An independent exhaustive Lean matching specification permits forbidden pairs, empty results and signed weights.')
        self.play(FadeIn(strip('MATHEMATICAL','dummy-assignment objective preservation',y=.42,accent=BLUE)))
        self.beat(notes='The source-level Rust integer assignment and partial matching adapters have total-correctness theorems for their checked contracts.')
        self.play(FadeIn(strip('RUST CORE','exact signed-i64 assignment and partial matching',y=-.72,accent=TEAL)))
        self.beat(notes='The full graph solver also needs the recurrence table, its wrapper, and efficient matching reuse connected to this core.')
        self.play(FadeIn(strip('INTEGRATION','graph-level Rust refinement is separate',y=-1.83,accent=AMBER)))
        self.finish()


class F09GraphProofs(MathPresentation):
    intro_notes = ('The two Droschinsky mathematical recurrences and '
                   'their reference evaluators are proved in Lean. Their '
                   'fast algorithmic schedule has additional obligations.')

    def construct(self):
        self.setup_page('Graph recurrences proved; speed still separate', 'Droschinsky 2016 and 2018',
                        'Droschinsky2016/RootedDynamicProgram.lean; Droschinsky2018/RootedDynamicProgram.lean')
        self.play(FadeIn(strip('2016','weighted branch matching recurrence and evaluation',y=1.42,accent=TEAL)))
        self.beat(notes='The 2016 reference table is proved optimal for the independent connected-subtree witness specification.')
        self.play(FadeIn(strip('2018','mapped/skipped recurrence and rooted evaluator',y=.33,accent=BLUE)))
        self.beat(notes='The 2018 mathematical objective includes topological paths and distance penalties. The reference evaluator enumerates matching choices.')
        self.play(FadeIn(strip('SHARED CORE','verified exact integer assignment and matching',y=-.75,accent=AMBER)))
        self.beat(notes='A proof of the published optimized time bound or of the whole graph-level Rust API does not follow from the reference theorem alone.')
        self.play(FadeIn(strip('OPEN','optimized graph runtimes and source refinement',y=-1.85,accent=ROSE)))
        self.finish()


class F10Research(MathPresentation):
    intro_notes = ('The research goal is to connect mathematical correctness '
                   'to usable high-performance implementations and test '
                   'the application-level value on a fair common task.')

    def construct(self):
        self.setup_page('What remains to make the full claim?', 'research program / open obligations',
                        'docs/planning/verified_common_subtree_research_program.md')
        show_rows(self,[
            ('EXACTNESS','optimized production witness provenance',TEAL,'Original-index reference endpoints are already proved. The optimized production witness and score correspondence remain open.'),
            ('OPTIMIZATION','matching reuse with derived source-level cost',BLUE,'Relate sparse assignment improvements to the published asymptotic analysis.'),
            ('INTEGRATION','Python/PyO3 correspondence and release gates',AMBER,'Independent parity tests already pass. Conversion source proofs and the final platform/release evidence remain distinct obligations.'),
            ('EVALUATION','strong baselines and fair downstream benchmarks',ROSE,'Measure accuracy, latency, memory and application-specific outcomes.'),
        ],start=1.43,step=1.12)
        self.finish()


class F11IndependentEvidence(MathPresentation):
    intro_notes = ('An independent finite oracle and systematic small-input '
                   'testing provide regression evidence distinct from the '
                   'general Lean theorems. Both are useful but have different scope.')

    def construct(self):
        self.setup_page('Independent oracles versus universal theorems', 'testing and proof have different scopes',
                        'proofs/checks/check_tree_contraction_oracle.py; Rust/OrderedSolver.lean')
        self.play(Write(formula(r'|\mathcal{T}_{\leq6}|=197',y=1.70,scale=1.07,color=TEAL)))
        self.beat(notes='There are 197 unlabeled rooted ordered trees through six edges. The independent Rust oracle compares all ordered pairs from this family.')
        self.play(Write(formula(r'197\times197=38809\ \mathrm{pairs}',y=.56,scale=.96,color=BLUE)))
        self.beat(notes='Those checks compare returned scores and structural witnesses to a separate exhaustive contraction oracle, rather than using Cython parity as the definition of correctness.')
        self.play(FadeIn(strip('FINITE TEST','find counterexamples and regressions',y=-.71,accent=AMBER)))
        self.beat(notes='The Lean theorem quantifies over all admissible inputs meeting its stated bounds, beyond these 38,809 examples.')
        self.play(FadeIn(strip('LEAN THEOREM','universal input guarantee within hypotheses',y=-1.76,accent=TEAL)))
        self.finish()


class F12Numbers(MathPresentation):
    intro_notes = ('An exact real-weight theorem and a checked integer '
                   'algorithm do not automatically certify a floating-point '
                   'public API. Zero-length results and negative scores also '
                   'depend on the API convention.')

    def construct(self):
        self.setup_page('Arithmetic and API boundaries', 'real / integer / floating-point',
                        'Shared/WeightedMatching; proofs/PROOF_STATUS.md')
        self.play(FadeIn(strip('REAL MODEL','exact scores, infinity sentinels in specifications',y=1.43,accent=TEAL)))
        self.beat(notes='The exact mathematical model can use real-valued weights and explicit negative infinity. It proves score identities without rounding.')
        self.play(FadeIn(strip('INTEGER RUST','signed-i64 code with checked arithmetic',y=.34,accent=BLUE)))
        self.beat(notes='The translated Rust integer algorithms require range and shape hypotheses, and return explicit errors for invalid inputs.')
        self.play(FadeIn(strip('FLOAT API','rounding, ties, overflow and nonfinite inputs',y=-.75,accent=AMBER)))
        self.beat(notes='A graph API that permits an empty result with score zero differs from a nonempty mathematical witness optimum. This choice must be reconciled explicitly.')
        self.play(FadeIn(strip('FEASIBILITY','empty versus nonempty connected witnesses',y=-1.82,accent=ROSE)))
        self.finish()


SCENES = [F01Question,F02Feasibility,F03Bridge,F04Countermodel,
          F05ReferenceProof,F06RustTranslation,F07RustMemo,
          F08Assignment,F09GraphProofs,F10Research,F11IndependentEvidence,F12Numbers]
