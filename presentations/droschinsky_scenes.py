"""Standalone Droschinsky--Kriege--Mutzel 2016 and 2018 lecture.

This deck connects the two different objective functions through their shared
bipartite matching subproblems, without conflating their feasibility relations.
"""
from __future__ import annotations

from manim import (Create, FadeIn, FadeOut, Write, Transform, Circle,
                   SurroundingRectangle, Arrow, GrowArrow, Line, VGroup, RIGHT, DOWN)

from scenes import MathPresentation, MathTex
from math_examples import node, EXAMPLE_MATCHING, max_weight_partial_matching, path_contribution
from math_examples import flip_augmenting_path, skipped_path_conflicts
from visuals import t, tree_drawing, panel, weight_matrix, TEAL, BLUE, AMBER, ROSE, FG, MUTED
from lecture_primitives import formula, strip, show_rows, center_text, side_formula


class D14AugmentingPath(MathPresentation):
    intro_notes = ('A weighted partial matching can require replacing an old '
                   'edge rather than greedily taking the largest edge. This '
                   'small alternating path illustrates a local repair, not '
                   'the full published matching schedule.')

    def construct(self):
        self.setup_page('Flip an alternating path', '2016 / matching and related instances',
                        'Tiny exhaustive matching oracle; no Hungarian runtime claim')
        weights = ((8, 7), (7, None))
        before = ((0, 0),)
        path = (('L', 1), ('R', 0), ('L', 0), ('R', 1))
        after = flip_augmenting_path(before, path)
        assert sum(weights[r][c] for r, c in after) == max_weight_partial_matching(weights)[0]
        points = {('L', 0): [-4.6, 1.2, 0], ('L', 1): [-4.6, -.55, 0],
                  ('R', 0): [-1.2, 1.2, 0], ('R', 1): [-1.2, -.55, 0]}
        vertex_mobs = {}
        for key, pos in points.items():
            vertex = Circle(radius=.28, color=BLUE).move_to(pos)
            label = t(('a', 'b')[key[1]] if key[0] == 'L' else ('x', 'y')[key[1]], 20).move_to(pos)
            vertex_mobs[key] = VGroup(vertex, label)
            self.play(Create(vertex), Write(label), run_time=.25)
        old = Line(points[('L', 0)], points[('R', 0)], buff=.30, color=TEAL, stroke_width=7)
        matrix = weight_matrix(weights, selected=before, x=3.25, y=1.2)
        status = self.text_at('Current weight: 8', 3.25, -.9, 24, TEAL)
        self.play(Create(old), FadeIn(matrix), Write(status),
                  FadeIn(self.text_at('× = forbidden', 3.25, -1.4, 18, MUTED)))
        self.beat(notes='b and y are free. Traverse the unused edge b-x, the matched edge x-a backwards, and the unused edge a-y.')
        arrows = VGroup()
        for source, target in zip(path, path[1:]):
            arrow = Arrow(points[source], points[target], buff=.32, color=AMBER, stroke_width=5)
            arrows.add(arrow)
            self.play(Create(arrow), run_time=.55)
        self.beat(notes='Flip path membership: remove a-x and add b-x and a-y. Weight changes by seven minus eight plus seven, gaining six.')
        new = VGroup(*(Line(points[('L', r)], points[('R', c)], buff=.30,
                            color=TEAL, stroke_width=7) for r, c in after))
        self.play(FadeOut(old), FadeOut(arrows), Create(new),
                  Transform(matrix, weight_matrix(weights, selected=after, x=3.25, y=1.2)),
                  Transform(status, self.text_at('New weight: 14', 3.25, -.9, 24, TEAL)))
        self.beat(notes='Related right-deletion instances use the same weight table with one column forbidden. Exhaustive optima are seven without x and eight without y. The 2016 optimization shares work between such instances.')
        deletion_scores = []
        for removed in range(2):
            reduced = tuple(tuple(w for j, w in enumerate(row) if j != removed) for row in weights)
            deletion_scores.append(max_weight_partial_matching(reduced)[0])
        self.play(FadeIn(strip('RELATED INSTANCES',
                              f'full: 14; delete x: {deletion_scores[0]}; delete y: {deletion_scores[1]}',
                              y=-2.15, accent=AMBER)))
        for removed, name in enumerate(('x', 'y')):
            self.beat(notes=f'Branch from the original table and remove {name}. The remaining weights are unchanged. This tiny optimum is obtained by independent enumeration; it illustrates related instances without claiming the paper optimized solver has been animated in full.')
            columns = [j for j in range(2) if j != removed]
            reduced = tuple(tuple(row[j] for j in columns) for row in weights)
            value, local_pairs = max_weight_partial_matching(reduced)
            original_pairs = tuple((r, columns[c]) for r, c in local_pairs)
            edges = VGroup(*(Line(points[('L', r)], points[('R', c)], buff=.30,
                                  color=TEAL, stroke_width=7) for r, c in original_pairs))
            next_matrix = weight_matrix(weights, selected=original_pairs, x=3.25, y=1.2)
            for r in range(2):
                next_matrix[2*r + removed].set_opacity(.15)
            self.play(Transform(new, edges), Transform(matrix, next_matrix),
                      Transform(status, self.text_at(f'Delete {name}: weight {value}', 3.25, -.9, 23, TEAL)),
                      *(vertex_mobs[('R', j)].animate.set_opacity(.15 if j == removed else 1)
                        for j in range(2)))
        self.play(FadeIn(center_text('Local repair, family reuse and total runtime need separate arguments.',
                                    y=-3.0, size=19)))
        self.finish()


class D15BranchCollision(MathPresentation):
    intro_notes = ('Two skeleton branches cannot share a skipped branch point. '
                   'Their host paths may intersect only at the mapped endpoint '
                   'they share in the skeleton.')

    def construct(self):
        self.setup_page('A skipped branch point cannot be shared', '2018 / skeleton validity',
                        'Droschinsky2018/Specification.lean; independent path-conflict example')
        host = node('r', node('x', node('a'), node('b')))
        drawing, positions = tree_drawing(host, anchor=(-3.3, 1.55), width=4.0, level_gap=1.05)
        self.play(Create(drawing))
        first = self.text_at('r -> x -> a', 3.0, 1.2, 26, TEAL)
        second = self.text_at('r -> x -> b', 3.0, .35, 26, AMBER)
        self.play(Write(first))
        left_path = VGroup(Line(positions[()], positions[(0,)], buff=.30, color=TEAL, stroke_width=8),
                           Line(positions[(0,)], positions[(0, 0)], buff=.30, color=TEAL, stroke_width=8))
        self.play(Create(left_path))
        self.beat(notes='Try to realize the other skeleton edge from the same mapped root r. Its path to b also passes through x.')
        right_path = VGroup(Line(positions[()], positions[(0,)], buff=.30, color=AMBER, stroke_width=5),
                            Line(positions[(0,)], positions[(0, 1)], buff=.30, color=AMBER, stroke_width=5))
        self.play(Write(second), Create(right_path))
        assert skipped_path_conflicts((('r', 'x', 'a'), ('r', 'x', 'b')), {'r', 'a', 'b'}) == {'x'}
        self.beat(notes='x is an interior vertex of both paths. This is forbidden even if the numeric score would look favorable; paying twice for x does not repair feasibility.')
        collision = Circle(radius=.42, color=ROSE, stroke_width=6).move_to(positions[(0,)])
        status = strip('INVALID', 'x belongs to both path interiors', y=-1.65, accent=ROSE)
        self.play(Create(collision), FadeIn(status))
        self.beat(notes='For a different freely rooted candidate, map the skeleton branch vertex to x itself. Then the two paths x-a and x-b intersect only at their shared mapped endpoint. This changes the mapping and its score.')
        assert not skipped_path_conflicts((('x', 'a'), ('x', 'b')), {'x', 'a', 'b'})
        valid = VGroup(Line(positions[(0,)], positions[(0, 0)], buff=.30, color=TEAL, stroke_width=7),
                       Line(positions[(0,)], positions[(0, 1)], buff=.30, color=TEAL, stroke_width=7))
        self.play(FadeOut(left_path), FadeOut(right_path), Create(valid),
                  collision.animate.set_color(TEAL),
                  Transform(first, self.text_at('x -> a', 3.0, 1.2, 26, TEAL)),
                  Transform(second, self.text_at('x -> b', 3.0, .35, 26, TEAL)),
                  Transform(status, strip('VALID CANDIDATE', 'x is now a mapped branch vertex', y=-1.65, accent=TEAL)))
        self.play(FadeIn(center_text('Freely choosing a mapped root differs from forcing r to remain mapped.',
                                    y=-2.9, size=19, color=AMBER)))
        self.finish()


class D01Question(MathPresentation):
    intro_notes = ('Droschinsky, Kriege and Mutzel study maximum common '
                   'structure in unrooted unordered trees with weights, '
                   'and then embeddings that skip vertices with penalties.')

    def construct(self):
        self.setup_page('Two weighted tree problems', 'Droschinsky--Kriege--Mutzel / 2016 and 2018',
                        'MFCS 2016 and MFCS 2018')
        one=node('u',node('a'),node('b',node('c')))
        two=node('v',node('q',node('r')),node('p'))
        left,_=tree_drawing(one,anchor=(-3.7,1.91),width=4.2,level_gap=.80)
        right,_=tree_drawing(two,anchor=(3.7,1.91),width=4.2,level_gap=.80)
        self.play(Create(left),Create(right))
        self.beat(notes='In 2016 we seek a connected subtree isomorphism; child order is irrelevant, and matched vertices and edges contribute weights.')
        self.play(FadeIn(strip('2016','weighted connected subtree isomorphism',y=-.75,accent=BLUE)))
        self.beat(notes='In 2018 an edge of the common skeleton may follow a path of length greater than one in an input, incurring a skipped-vertex penalty.')
        self.play(FadeIn(strip('2018','topological embeddings with distance penalties',y=-1.74,accent=TEAL)))
        self.play(FadeIn(center_text('Both reduce branch choices to weighted matchings.',y=-2.75,size=22,color=AMBER)))
        self.finish()


class D02Unordered(MathPresentation):
    intro_notes = ('Unlike the ordered-tree algorithm, permutation of '
                   'children does not invalidate an isomorphism. Their '
                   'disjoint branch associations become a matching.')

    def construct(self):
        self.setup_page('Why child order disappears', 'unrooted and unordered inputs',
                        'Droschinsky--Kriege--Mutzel 2016 / Section 2')
        a=node('u',node('a'),node('b'))
        b=node('v',node('b'),node('a'))
        left,_=tree_drawing(a,anchor=(-3.5,1.20),width=4)
        right,_=tree_drawing(b,anchor=(3.5,1.20),width=4)
        self.play(Create(left),Create(right))
        self.beat(notes='The two displayed child configurations represent the same unordered branching structure when corresponding labels match.')
        self.play(Write(formula(r'\pi:\{a,b\}\longrightarrow\{b,a\}',y=-.63,scale=.95,color=TEAL)))
        self.beat(notes='Each selected child subtree on the left can be paired to at most one child subtree on the right, and vice versa.')
        self.play(FadeIn(strip('INJECTIVITY','no child can participate twice',y=-1.65,accent=AMBER)))
        self.beat(notes='Unmatched branches can be omitted. Consequently the correct combinatorial subproblem is partial rather than mandatory perfect matching.')
        self.play(FadeIn(center_text('An unmatched child is allowed.',y=-2.73,size=23,color=FG)))
        self.finish()


class D03Score(MathPresentation):
    intro_notes = ('The connected common subtree score sums selected vertex '
                   'and edge pair weights. The contribution of a branch '
                   'consists of its matched parent edge and its optimal descendant.')

    def construct(self):
        self.setup_page('What exactly is optimized in 2016?', 'weighted isomorphism objective',
                        'Droschinsky2016/Specification.lean; RootedRecurrence.lean')
        self.play(Write(formula(r'W(\varphi)=\sum_{u\ \mathrm{mapped}}w_V(u,\varphi(u))',y=1.65,scale=.84)))
        self.beat(notes='Every mapped vertex pair contributes a score; it may be negative in the general mathematical specification.')
        self.play(Write(formula(r'\quad+\sum_{uv\ \mathrm{mapped}}w_E(uv,\varphi(u)\varphi(v))',y=.52,scale=.86,color=BLUE)))
        self.beat(notes='A feasible witness must preserve connected adjacency and be injective; a high-scoring collection of disconnected pairs is not admissible.')
        self.play(FadeIn(strip('FEASIBLE','injective, adjacency preserving, connected',y=-.77,accent=TEAL)))
        self.beat(notes='A rooted subproblem fixes mapped endpoints u and v, but the unrestricted optimum may choose its own roots and orientation.')
        self.play(FadeIn(strip('ROOTED STATE','specified roots u and v map to one another',y=-1.78,accent=AMBER)))
        self.play(FadeIn(center_text('Scoring and feasible mappings are separate contracts.',y=-2.79,size=21)))
        self.finish()


class D04RootRecurrence(MathPresentation):
    intro_notes = ('When the two roots are mapped, their selected branches '
                   'form a partial matching between their children. This '
                   'decomposition justifies the rooted recurrence.')

    def construct(self):
        self.setup_page('Deriving the rooted recurrence', '2016 / branch decomposition',
                        'Droschinsky2016/OrientedRecurrence.lean')
        self.play(Write(formula(r'F(u,v)=w_V(u,v)+\operatorname{MWM}(C_{u,v})',y=1.73,scale=.89,color=TEAL)))
        self.beat(notes='A candidate child edge u to a and v to b earns the two edge correspondence weight plus the already optimized descendant score.')
        self.play(Write(formula(r'C_{u,v}(a,b)=w_E(ua,vb)+F(a,b)',y=.47,scale=.87,color=BLUE)))
        self.beat(notes='A matching is exactly the set of disjoint branch pairings; each selected pairing contributes independently after the roots are fixed.')
        self.play(FadeIn(strip('LOCAL CHOICE','choose a disjoint set of child pairs',y=-.77,accent=AMBER)))
        self.beat(notes='Proof obligations run in both directions: restrict an arbitrary witness to child branches; then graft any feasible matching of child witnesses together.')
        self.play(FadeIn(strip('TWO DIRECTIONS','decompose each witness; assemble each matching',y=-1.72,accent=TEAL)))
        self.play(FadeIn(center_text('This is equality of optima, not a heuristic recurrence.',y=-2.74,size=21)))
        self.finish()


class D05MatchingAlternatives(MathPresentation):
    intro_notes = ('A two-row, three-column matrix makes partial matching '
                   'and disjointness visible. The optimum is fifteen, using '
                   'the entries eight and seven.')

    def construct(self):
        self.setup_page('Solve one partial matching', '2016 / explicit matrix example',
                        'SubtreeProofs/Shared/WeightedMatching.lean')
        matrix=weight_matrix(EXAMPLE_MATCHING,x=0,y=1.12,size=1.06)
        self.play(FadeIn(matrix))
        self.beat(notes='Choose the eight in row one, column one. No further edge may reuse that row or that column.')
        mark1=SurroundingRectangle(matrix[0],buff=.06,color=TEAL)
        self.play(Create(mark1))
        self.beat(notes='Choose seven in row two, column two, which shares no endpoint with the first selected edge.')
        mark2=SurroundingRectangle(matrix[4],buff=.06,color=TEAL)
        self.play(Create(mark2))
        self.beat(notes='Alternative matchings such as eight plus two or four plus three score below fifteen.')
        self.play(Write(formula(r'\max_{M\ \mathrm{partial}}\sum_{(i,j)\in M}C_{ij}=8+7=15',y=-1.65,scale=.85,color=TEAL)))
        self.play(FadeIn(center_text('One selected edge per row and per column.',y=-2.76,size=22)))
        self.finish()


class D06Assignment(MathPresentation):
    intro_notes = ('The mathematically exact matching specification allows '
                   'forbidden pairs and unmatched endpoints. A reduction '
                   'to square assignment introduces dummy vertices, then decodes.')

    def construct(self):
        self.setup_page('From partial matching to assignment', 'algorithmic reduction',
                        'Shared/WeightedMatching/AssignmentReduction.lean')
        self.play(Write(formula(r'|L|=k,\quad |R|=\ell',y=1.68,scale=1.12,color=TEAL)))
        self.beat(notes='Add dummy slots to turn optional matches into a full permutation. This is a mathematical construction, not a large numeric sentinel trick.')
        self.play(Write(formula(r'N=k+\ell',y=.53,scale=1.29,color=BLUE)))
        self.beat(notes='Zero-profit dummy choices represent omitted endpoints. Forbidden pairs are ruled out by the reduction and decoded solution contract.')
        self.play(FadeIn(strip('ENCODE','legal partial matching to a square permutation',y=-.72,accent=AMBER)))
        self.beat(notes='The exact reduction proves decoded objective preservation over real weights. Floating point correctness requires its own treatment.')
        self.play(FadeIn(strip('DECODE','restore original indices and exact selected pairs',y=-1.66,accent=TEAL)))
        self.play(FadeIn(center_text('A matching library must preserve the objective.',y=-2.72,size=22)))
        self.finish()


class D07Rerooting(MathPresentation):
    intro_notes = ('An unrooted subtree has a uniquely distinguished top '
                   'vertex relative to any chosen ambient root. This permits '
                   'fixed-root reductions, but rerooting naively can be costly.')

    def construct(self):
        self.setup_page('From rooted to unrooted subtrees', '2016 / fixed-root reduction',
                        'Droschinsky2016/Rooted.lean; RootedDynamicProgram.lean')
        self.play(Write(formula(r'\operatorname{OPT}_{\rm unrooted}(G,H)',y=1.62,scale=1.02,color=TEAL)))
        self.beat(notes='Any connected mapped subtree has a top vertex in each ambient orientation, giving a candidate rooted component.')
        self.play(Write(formula(r'=\max_{u\in G,\ v\in H}F_{u,v}',y=.55,scale=1.06,color=BLUE)))
        self.beat(notes='The recurrence can be evaluated in fixed orientations. Its proof is separate from the optimized schedule for all root pairs.')
        self.play(FadeIn(strip('CORRECTNESS','finite rooted family suffices',y=-.75,accent=TEAL)))
        self.beat(notes='The 2016 paper reuses related matching instances instead of solving every root configuration independently.')
        self.play(FadeIn(strip('OPTIMIZATION','related matching instances can share work',y=-1.76,accent=AMBER)))
        self.play(FadeIn(center_text('Naive rerooting proves a baseline, not the fast bound.',y=-2.77,size=20)))
        self.finish()


class D08Topology(MathPresentation):
    intro_notes = ('The 2018 model permits paths in the host trees for edges '
                   'of a common skeleton. Internal vertices of those paths '
                   'cannot be mapped branch vertices.')

    def construct(self):
        self.setup_page('A common edge can become a path', '2018 / topological embedding',
                        'Droschinsky2018/Specification.lean')
        direct=node('u',node('v'))
        extended=node('u',node('x',node('v')))
        a,_=tree_drawing(direct,anchor=(-3.6,1.33),width=3.8)
        b,_=tree_drawing(extended,anchor=(3.6,1.33),width=3.8,dim=((0,),))
        self.play(Create(a),Create(b))
        self.beat(notes='Both sides map the same abstract skeleton edge. On the right, the host route is two edges with skipped internal vertex x.')
        self.play(Write(formula(r'\operatorname{length}_L=1,\quad \operatorname{length}_R=2',y=-1.25,scale=.83,color=TEAL)))
        self.beat(notes='Paths for distinct skeleton edges may meet at their shared mapped endpoints, but their interior cannot be reused in another branch.')
        self.play(FadeIn(strip('INTERIORS','skipped vertices remain distinct and unmapped',y=-2.15,accent=AMBER)))
        self.play(FadeIn(center_text('The 2018 feasible set is larger than edge isomorphism.',y=-2.94,size=21)))
        self.finish()


class D09TwoStateTrace(MathPresentation):
    intro_notes = ('The 2018 recurrence has mapped and skipped states. '
                   'The mapped branch chooses between connecting children '
                   'directly and using an intervening skipped path.')

    def construct(self):
        self.setup_page('Evaluate the two-state branch choice', '2018 / mapped and skipped',
                        'Droschinsky2018/SkippedRecurrence.lean; RootedDynamicProgram.lean')
        self.play(Write(formula(r'M(u,v)=w_V(u,v)+\mathrm{MWM}(C_{u,v})',y=1.72,scale=.81,color=TEAL)))
        self.beat(notes='A child pair can attach directly to the mapped parent. That earns the edge-pair reward and the mapped child state.')
        self.play(Write(formula(r'C_{u,v}(c,d)=\max\{w_E+M(c,d),\ S(c,d)\}',y=.47,scale=.79,color=BLUE)))
        self.beat(notes='The skipped state moves down one side and charges a one-vertex penalty. It also permits further skip steps by recurrence.')
        self.play(Write(formula(r'S(u,v)=-p+\max\{\mathrm{child\ states}\}',y=-.74,scale=.83,color=AMBER)))
        self.beat(notes='In the Lean reference evaluator, dependency states are read from a finite table and the matching is solved exhaustively. Optimized matching complexity is a separate result.')
        self.play(FadeIn(center_text('Mapped = retain endpoints.  Skipped = advance through a path.',y=-2.42,size=21)))
        self.finish()


class D10Bounds(MathPresentation):
    intro_notes = ('The published asymptotic results are important '
                   'but their optimized implementation requires additional '
                   'matching reuse, scheduling and arithmetic arguments.')

    def construct(self):
        self.setup_page('What the fast algorithms establish', 'published bounds versus verified reference',
                        '2016 arXiv v4, Theorem 4; 2018 arXiv v1, Theorem 15')
        self.play(Write(formula(r'\mathrm{2016:}\quad O(|G|\,|H|\,(\delta+\log D))',y=1.65,scale=.88,color=BLUE)))
        self.play(Write(formula(r'\delta=\min(\Delta_G,\Delta_H),\quad D=\max(\Delta_G,\Delta_H)',
                                y=.99,scale=.60,color=MUTED)))
        self.beat(notes='For unrestricted weights, the pinned 2016 v4 bound keeps both degree parameters and the logarithmic term. An unqualified n-squared-delta expression loses that distinction.')
        self.play(Write(formula(r"\mathrm{2018:}\quad O(|T|\,|T'|\,\min(\Delta_T,\Delta_{T'}))",y=.30,scale=.80,color=TEAL)))
        self.beat(notes='The 2018 real-weight bound uses the smaller maximum degree. Correctness of reference recurrences does not imply either optimized cost theorem.')
        self.play(FadeIn(strip('LEAN RESULTS','recurrences and witness decompositions proved',y=-.75,accent=TEAL)))
        self.beat(notes='The current Lean reference graph evaluators use repeated or exhaustive matchings; their implementation cost does not inherit the paper fast bounds.')
        self.play(FadeIn(strip('REMAINING','optimized graph runtime and Rust refinement',y=-1.73,accent=AMBER)))
        self.play(FadeIn(center_text('Proving the recurrence does not certify an optimized runtime.',y=-2.77,size=20)))
        self.finish()


class D11DualCut(MathPresentation):
    intro_notes = ('The 2016 matching reuse strategy has an assignment '
                   'subproblem with dual feasibility and tight edges. '
                   'A search cut can be adjusted until a new tight edge appears.')

    def construct(self):
        self.setup_page('How a dual search makes progress', '2016 / matching reuse mechanism',
                        'Shared/AssignmentSparseSearch.lean; Rust/SparseCutStep.lean')
        self.play(Write(formula(r'r_{ij}=c_{ij}-u_i-v_j\geq0',y=1.65,scale=1.06,color=TEAL)))
        self.beat(notes='In the minimum-cost assignment view, feasible dual potentials leave every allowed reduced cost nonnegative. Selected edges with reduced cost zero are tight.')
        self.play(FadeIn(strip('TIGHT EDGE','reduced cost exactly zero',y=.43,accent=BLUE)))
        self.beat(notes='Given a nonterminal alternating-search cut, choose the smallest reduced cost of an allowed edge leaving the cut. Adjust selected row and column potentials.')
        self.play(Write(formula(r'\delta=\min_{(i,j)\in\mathrm{crossing}}r_{ij}',y=-.72,scale=.90,color=AMBER)))
        self.beat(notes='The updated dual remains feasible and creates a new tight crossing edge; the search can extend or reach the free target.')
        self.play(FadeIn(strip('PROGRESS','new tight crossing edge; old matches stay tight',y=-1.78,accent=TEAL)))
        self.finish()


class D12DeletionReuse(MathPresentation):
    intro_notes = ('When only one vertex is removed between related matching '
                   'instances, most of a previous optimum may be reusable. '
                   'The proof first establishes the size of the resulting deficit.')

    def construct(self):
        self.setup_page('Why deleting one vertex can be cheaper', '2016 / related matching instances',
                        'Shared/MatchingDeletion.lean; PROOF_STATUS.md')
        self.play(Write(formula(r'M^\star\ \leadsto\ M^\star\setminus\{(i,j)\}',y=1.66,scale=1.05,color=TEAL)))
        self.beat(notes='Removing a matched endpoint destroys at most one edge of the old matching. Many unaffected pairs remain valid.')
        self.play(FadeIn(strip('SURVIVORS','retain unchanged disjoint edges',y=.47,accent=BLUE)))
        self.beat(notes='The remaining instance can often be repaired by an alternating path or cycle search rather than solved from scratch.')
        self.play(FadeIn(strip('REPAIR','search for one local augmenting correction',y=-.61,accent=AMBER)))
        self.beat(notes='Correctness of a local repair and the claimed faster asymptotic schedule are separate arguments; the Rust optimized deletion driver is not yet fully verified.')
        self.play(FadeIn(strip('PROOF EDGE','optimized reuse and total runtime remain open',y=-1.72,accent=ROSE)))
        self.finish()


class D13Unrooted2018(MathPresentation):
    intro_notes = ('The 2018 paper also treats unrooted topological '
                   'embeddings. A simple correct baseline tries all ambient '
                   'root pairs; the optimized theorem avoids paying the full cost.')

    def construct(self):
        self.setup_page('The unrooted 2018 problem', 'root choice and shared work',
                        'Droschinsky2018/RootedDynamicProgram.lean; MFCS 2018 Theorem 15')
        self.play(Write(formula(r"\max_{r\in T,\ s\in T' }\operatorname{Mapped}_{r,s}(r,s)",y=1.65,scale=.85,color=TEAL)))
        self.beat(notes='Trying all root pairs and evaluating a rooted table in each orientation gives a correct baseline over all connected common embeddings.')
        self.play(FadeIn(strip('BASELINE','enumerate roots and evaluate each orientation',y=.43,accent=BLUE)))
        self.beat(notes='The published method reuses related branch matching instances and maxima across configurations to reduce the total work.')
        self.play(FadeIn(strip('PAPER METHOD','share matching values and root information',y=-.61,accent=AMBER)))
        self.beat(notes='The paper proves an O of n times m times minimum-maximum-degree bound. The full optimized unrooted schedule remains an open Lean endpoint in this repository.')
        self.play(FadeIn(strip('PROOF STATUS','reference correct; fast schedule not yet verified',y=-1.71,accent=ROSE)))
        self.finish()


SCENES = [D01Question,D02Unordered,D03Score,D04RootRecurrence,
          D05MatchingAlternatives,D06Assignment,D07Rerooting,D08Topology,
          D09TwoStateTrace,D10Bounds,D11DualCut,D12DeletionReuse,D13Unrooted2018,
          D14AugmentingPath,D15BranchCollision]
