"""Standalone Lozano--Valiente (2004) mathematical talk.

The source paper's printed containment grammar and its algorithmic contraction
objective are deliberately separated: they have different extension sets.
"""
from __future__ import annotations

from manim import (VGroup, FadeIn, FadeOut, Create, Write, Transform,
                   SurroundingRectangle, Arrow, Line, RIGHT, UP, DOWN)

from scenes import MathPresentation, MathTex
from math_examples import (node, encode_tree, decode_tree, contract_edge,
                           common_embedding_oracle, lozano_recurrence_candidate_scores,
                           split_first_pair, all_contractions)
from visuals import t, tree_drawing, panel, TEAL, BLUE, AMBER, ROSE, FG, MUTED
from lecture_primitives import formula, strip, show_rows, center_text, side_formula


class L01Question(MathPresentation):
    intro_notes = ('Lozano and Valiente study largest common embedded subtrees '
                   'for rooted ordered trees. We retain relative sibling order and '
                   'may contract parent-child edges in both inputs.')

    def construct(self):
        self.setup_page('Common structure in ordered trees', 'Lozano--Valiente 2004 / problem',
                        'On the Maximum Common Embedded Subtree Problem for Ordered Trees')
        first = node('r', node('a', node('b'), node('c')))
        second = node('s', node('x', node('y')), node('z'))
        a, _ = tree_drawing(first, anchor=(-3.55, 1.0), width=4.6)
        b, _ = tree_drawing(second, anchor=(3.55, 1.0), width=4.6)
        self.play(Create(a), Create(b))
        self.beat(notes='A common answer must be reachable by contractions in both trees. It is a tree-shaped witness, not just a similarity number.')
        self.play(Write(formula(r'C\preccurlyeq A,\quad C\preccurlyeq B', y=-.60, color=TEAL)))
        self.beat(notes='The objective counts retained edges. The zero-edge singleton is always feasible when labels are ignored.')
        self.play(Write(formula(r'\max_{C\preccurlyeq A,\ C\preccurlyeq B}\ |E(C)|', y=-1.63, color=AMBER)))
        self.beat(notes='The answer is a concrete contracted tree. Later we show a Dyck-word recurrence that calculates its size and a witness.')
        self.play(FadeIn(center_text('What can survive in both trees?',y=-2.79,size=25,color=FG)))
        self.finish()


class L02Order(MathPresentation):
    intro_notes = ('Ordered means sibling positions matter. The left-to-right '
                   'relationship survives contraction; it is not a free matching '
                   'of unordered neighbor sets.')

    def construct(self):
        self.setup_page('Order is part of the feasible mapping', 'ordered versus unordered',
                        'Lozano--Valiente (2004), Section 2')
        a = node('r', node('A'), node('B'))
        b = node('r', node('B'), node('A'))
        left, _ = tree_drawing(a, anchor=(-3.7, 1.35),width=3.7)
        right, _ = tree_drawing(b, anchor=(3.7, 1.35),width=3.7)
        self.play(Create(left), Create(right))
        self.beat(notes='If labels A and B must agree, swapping the two children is invalid for an order-preserving isomorphism.')
        self.play(FadeIn(center_text('Left-to-right order is preserved',y=-.72,size=27,color=ROSE)))
        self.beat(notes='Contraction of an internal edge may splice that vertex\'s children into the parent while keeping their relative order.')
        self.play(Write(formula(r'(a,b,c)\longrightarrow(a,b_1,b_2,c)',y=-1.56,scale=.8,color=TEAL)))
        self.beat(notes='The paper starts from unlabeled structure; label affinity is a separate extension and changes the scoring contract.')
        self.play(FadeIn(center_text('Labels and affinities are additional constraints.', y=-2.62, size=22)))
        self.finish()


class L03Factorization(MathPresentation):
    intro_notes = ('Every nonempty balanced word has a unique first-return '
                   'factorization of the form zero, interior, one, suffix.')

    def construct(self):
        self.setup_page('First-return decomposition', 'Catalan / Dyck-word structure',
                        'Paper2004/BalancedSequence.lean; Decomposition.lean')
        self.play(Write(formula(r'w=0\,x\,1\,y',y=1.66,scale=1.25,color=TEAL)))
        self.beat(notes='The first zero descends to the first child, and its matching one closes that child subtree. The interior x describes descendants.')
        self.play(Write(formula(r'001011=0\ \underbrace{0101}_{x}\ 1\ \underbrace{\varepsilon}_{y}',y=.52,scale=.95)))
        self.beat(notes='After the first-return pair, the remaining balanced suffix y describes the subsequent siblings. Here there is no suffix.')
        self.play(FadeIn(strip('INTERIOR x','ordered children of first child',y=-.67,accent=BLUE)))
        self.beat(notes='This factorization induces a recursive tree description and supplies three cases for the maximum-common-substructure recurrence.')
        self.play(FadeIn(strip('SUFFIX y','ordered siblings after first child',y=-1.64,accent=AMBER)))
        self.play(FadeIn(center_text('Factorization is unique; both parts remain balanced.',y=-2.75,size=22)))
        self.finish()


class L04PrintedGap(MathPresentation):
    intro_notes = ('The printed recursive containment relation in Definition 2 '
                   'does not capture every matched-pair contraction. The Lean '
                   'development preserves both relations and proves a counterexample.')

    def construct(self):
        self.setup_page('A precise gap in printed containment', 'Definition 2 versus contraction',
                        'Paper2004/PrintedContainmentCounterexample.lean')
        self.play(Write(formula(r'001011\longrightarrow0011',y=1.62,scale=1.30,color=TEAL)))
        self.beat(notes='Delete the matched pair for one leaf beneath the internal vertex. This gives a valid two-edge path.')
        left = node('r',node('a',node('b'),node('c')))
        right = contract_edge(left,(0,1))
        a,_=tree_drawing(left,anchor=(-3.8,.99),width=3.7)
        b,_=tree_drawing(right,anchor=(3.8,.99),width=3.7)
        self.play(Create(a),Create(b))
        self.beat(notes='The least relation generated by the literal printed recursion admits only 001011, 0101, 01, and the empty word on this input.')
        self.play(FadeIn(center_text('Printed outcomes: 001011, 0101, 01, empty',y=-1.77,size=24,color=ROSE)))
        self.beat(notes='The operational contraction relation includes 0011. The paper algorithm is analyzed against operational containment rather than the incomplete literal grammar.')
        self.play(FadeIn(center_text('Operational containment has strictly more witnesses.',y=-2.73,size=22,color=AMBER)))
        self.finish()


class L05ValueTrace(MathPresentation):
    intro_notes = ('A small instance exposes all three branches of Lemma 8 '
                   'and allows an independent check against exhaustive tree contractions.')

    def construct(self):
        self.setup_page('Evaluate the recurrence on a real pair', 'Lemma 8 / worked example',
                        'Paper2004/DynamicProgram.lean; checks/check_paper_dp_recurrence.py')
        a,b='001011','0011'
        vals=lozano_recurrence_candidate_scores(a,b)
        oracle,_=common_embedding_oracle(decode_tree(a),decode_tree(b))
        self.play(Write(formula(r'(a,b)=(001011,0011)',y=1.72,scale=1.04,color=TEAL)))
        lines=[
            ('MATCH FIRST',f'1 + L(x,u) + L(y,v) = {vals[0]}',TEAL,'The pair survives in both words. Add the recursive interior and sibling scores.'),
            ('DROP IN A',f'L(x+y,b) = {vals[1]}',AMBER,'Contract the first pair of a and compare against all of b.'),
            ('DROP IN B',f'L(a,u+v) = {vals[2]}',ROSE,'Contract the first pair of b and compare against all of a.'),
        ]
        show_rows(self,lines,start=.57,step=.98)
        self.beat(notes='The best score is two and the exhaustive independent contraction oracle returns the same optimum.')
        self.play(Write(formula(r'\max\{'+','.join(map(str,vals))+r'\}='+str(oracle),y=-2.68,color=TEAL)))
        self.finish()


class L06Witness(MathPresentation):
    intro_notes = ('The recurrence is a constructive algorithm. A branch '
                   'choice must reconstruct a feasible common tree, not merely '
                   'attain an integer score.')

    def construct(self):
        self.setup_page('From score to common witness', 'constructive correctness',
                        'Paper2004/OptimalEncoding.lean; DynamicProgram.lean')
        a,b=node('r',node('a',node('b'),node('c'))),node('s',node('x',node('y')))
        score,word=common_embedding_oracle(a,b)
        self.play(Write(formula(r'\operatorname{OPT}(A,B)=2',y=1.63,scale=1.18,color=AMBER)))
        self.beat(notes='The independent exhaustive oracle selects a common contraction with two retained edges. Its balanced word represents that witness.')
        self.play(Write(formula(r'\operatorname{enc}(C)='+word,y=.46,scale=1.1,color=TEAL)))
        self.beat(notes='The same C can be obtained from both original trees by edge contractions. The encoding and decoding round trips are separately proved.')
        w,_=tree_drawing(decode_tree(word),anchor=(0,-.25),width=4.0,level_gap=.74)
        self.play(Create(w))
        self.beat(notes='A numeric maximum with no feasible witness would be weaker. The theorem establishes the existence and optimality of an explicit common tree.')
        self.play(FadeIn(center_text('Feasible in both inputs; no larger common contraction exists.',y=-2.77,size=20)))
        self.finish()


class L07StateBound(MathPresentation):
    intro_notes = ('Memoization is effective because a structural decomposition '
                   'bounds the set of distinct relevant balanced-word states.')

    def construct(self):
        self.setup_page('Why memoization reduces the search', 'state counting and costs',
                        'Paper2004/Decomposition.lean; MemoizedDynamicProgram.lean')
        self.play(Write(formula(r'|D(T)|\ \leq\ (n+1)\ell',y=1.67,scale=1.05,color=TEAL)))
        self.beat(notes='The D-family cardinality is bounded using the actual leaf count and the depth structure. Here n is the edge or size parameter in the corresponding lemma.')
        self.play(Write(formula(r'\mathrm{states}\subseteq D(A)\times D(B)',y=.58,scale=.98,color=BLUE)))
        self.beat(notes='Cached subproblems are pairs of decomposition states. Their product is finite, and the memoized recurrence does not add the same key twice.')
        self.play(FadeIn(strip('STATE BOUND','proved structural state family',y=-.68,accent=TEAL)))
        self.beat(notes='The actual Lean cache is an association list; linear lookup adds another comparison factor. Expected constant-time hashing is not yet a verified implementation cost.')
        self.play(FadeIn(strip('CACHE COST','association-list scans are counted',y=-1.66,accent=AMBER)))
        self.play(FadeIn(center_text('State count and wall-clock runtime are different claims.',y=-2.74,size=21,color=FG)))
        self.finish()


class L08StructuralCases(MathPresentation):
    intro_notes = ('The proof of the ordered recurrence does not simply '
                   'assume that one of three plausible formulas is correct. '
                   'It classifies the first annotated pairs of a common witness.')

    def construct(self):
        self.setup_page('Why the three cases are complete', 'Lemma 8 / proof idea',
                        'Paper2004/DynamicProgram.lean / dyckEmbeds_first_pair')
        self.play(Write(formula(r'a=0x1y,\qquad b=0u1v',y=1.73,scale=.98,color=TEAL)))
        self.beat(notes='If both first matched pairs survive in the witness, the witness divides into an interior common contraction and a suffix common contraction.')
        self.play(FadeIn(strip('KEEP BOTH','1 + L(x,u) + L(y,v)',y=.59,accent=TEAL)))
        self.beat(notes='If the first pair of a does not survive, remove it and recurse on x concatenated with y versus b.')
        self.play(FadeIn(strip('DROP LEFT','L(x+y,b)',y=-.45,accent=AMBER)))
        self.beat(notes='Otherwise one may remove the first pair of b and recurse on a versus u concatenated with v. Every feasible witness fits one branch.')
        self.play(FadeIn(strip('DROP RIGHT','L(a,u+v)',y=-1.47,accent=ROSE)))
        self.play(FadeIn(center_text('Exhaustive case split + witness construction = optimality.',y=-2.74,size=20)))
        self.finish()


class L09ShapeSensitivity(MathPresentation):
    intro_notes = ('The published ordered-tree bound depends on depth '
                   'and leaf count. This refines a uniform cubic-style '
                   'worst-case description by using tree shape.')

    def construct(self):
        self.setup_page('How tree shape enters the complexity', 'depth and leaves',
                        'Lozano--Valiente (2004), Theorem 3; TreeStateBounds.lean')
        chain=node('r',node('a',node('b',node('c'))))
        star=node('r',node('a'),node('b'),node('c'))
        a,_=tree_drawing(chain,anchor=(-3.6,2.10),width=2.6,level_gap=.71)
        b,_=tree_drawing(star,anchor=(3.6,2.10),width=4.2,level_gap=.79)
        self.play(Create(a),Create(b))
        self.beat(notes='A chain has high depth and few leaves, whereas a star has shallow depth and many leaves. Both are shaped differently with the same number of edges.')
        self.play(FadeIn(strip('CHAIN','depth 3, leaves 1, minimum 1',y=-.72,accent=TEAL)))
        self.beat(notes='For the star, depth one and three leaves also make the minimum equal to one. Other shapes interpolate between these extreme values.')
        self.play(FadeIn(strip('STAR','depth 1, leaves 3, minimum 1',y=-1.72,accent=AMBER)))
        self.beat(notes='The paper bound multiplies the two trees\' size parameters and their minimum depth-or-leaf parameters. A full source-level runtime proof also needs operation costs.')
        self.play(FadeIn(center_text('O(n1 n2 min(d1,l1) min(d2,l2))',y=-2.75,size=21,color=FG)))
        self.finish()


SCENES = [L01Question,L02Order,L03Factorization,L04PrintedGap,
          L05ValueTrace,L06Witness,L07StateBound,L08StructuralCases,L09ShapeSensitivity]
