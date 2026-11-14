"""Animated mathematical presentation: Lozano-Valiente and Droschinsky.

Render: manim -qh presentations/scenes.py AllProblems (or ./presentations/render.py)
Optional interactive mode: pip install manim-slides; render with manim-slides.
No binary assets or repository implementations are required to render.
"""
from __future__ import annotations

from manim import (
    Scene, VGroup, Text, MathTex as ManimMathTex, TexTemplate, FadeIn, FadeOut, Create, Write,
    Transform, TransformMatchingTex, ReplacementTransform, GrowArrow,
    Arrow, Line, Rectangle, RoundedRectangle, SurroundingRectangle, Circle,
    DashedLine, RIGHT, LEFT, UP, DOWN, ORIGIN, WHITE, config,
)

try:
    from manim_slides import Slide as _SlideBase
except ImportError:
    _SlideBase = Scene

from math_examples import (
    EXAMPLE_BRANCHING, EXAMPLE_REDUCED, EXAMPLE_MATCHING,
    node, encode_tree, lozano_dp_word, max_weight_partial_matching,
    path_contribution,
)
from visuals import (
    BG, FG, MUTED, TEAL, AMBER, ROSE, BLUE, PANEL, PANEL_BORDER,
    card, panel, t, tree_drawing, weight_matrix,
)

# Use one explicit LaTeX template for every mathematical expression.  The
# narration uses ordinary Manim Text where possible.  In particular,
# \text and \operatorname require amsmath; relying on a global template can
# make an otherwise valid scene fail only after several seconds of rendering.
PRESENTATION_TEX_TEMPLATE = TexTemplate()
PRESENTATION_TEX_TEMPLATE.add_to_preamble(r"\usepackage{amsmath}")
PRESENTATION_TEX_TEMPLATE.add_to_preamble(r"\usepackage{amssymb}")


def MathTex(*expressions, **kwargs):
    """Construct presentation mathematics with the pinned LaTeX preamble."""
    kwargs.setdefault("tex_template", PRESENTATION_TEX_TEMPLATE)
    return ManimMathTex(*expressions, **kwargs)


# Video-oriented scenes also work as click-advanced manim-slides if installed.
# All page layouts target the default Manim 16:9 frame (14.222 x 8 units).


class MathPresentation(_SlideBase):
    def setup_page(self, title, tag, source=""):
        config.background_color = BG
        heading = t(title, 41, FG).to_edge(UP, buff=.45).align_to(LEFT * 6.40, LEFT)
        section = t(tag.upper(), 18, TEAL).next_to(heading, DOWN, buff=.16).align_to(heading, LEFT)
        line = Line([-6.40, 2.42, 0], [6.40, 2.42, 0], color=PANEL_BORDER, stroke_width=2)
        source_line = t(source, 13, MUTED) if source else t("Common subtree mathematics", 13, MUTED)
        source_line.move_to([0, -3.72, 0])
        self.add(heading, section, line, source_line)

    def beat(self, seconds=1.0):
        if hasattr(self, "next_slide"):
            self.next_slide()
        else:
            self.wait(seconds)

    def text_at(self, value, x, y, size=25, color=FG):
        return t(value, size=size, color=color).move_to([x, y, 0])


class AllProblems(MathPresentation):
    """Three related but mathematically distinct optimization problems."""
    def construct(self):
        self.setup_page("Maximum common structure in trees", "The three problem families",
                        "Lozano-Valiente (2004); Droschinsky et al. (2016, 2018)")
        left = card("ORDERED", "Embedded subtrees\nedge contractions\nrelative child order", TEAL, 3.85, 2.75)
        mid = card("UNORDERED", "Weighted isomorphism\nchild permutations\nbipartite matching", AMBER, 3.85, 2.75)
        right = card("TOPOLOGICAL", "Skipped vertices\ndistance penalties\npath constraints", ROSE, 3.85, 2.75)
        for c, x in zip((left, mid, right), (-4.22, 0, 4.22)):
            c.move_to([x, .50, 0])
        self.play(FadeIn(left), FadeIn(mid), FadeIn(right), run_time=1.7)
        core = self.text_at("Different feasible mappings  ->  different objective functions", 0, -2.15, 25)
        self.play(Write(core))
        self.beat()


class OrderedContraction(MathPresentation):
    """Operational semantics: remove an edge, splice the child's children."""
    def construct(self):
        self.setup_page("Ordered edge contraction", "Lozano-Valiente / semantics",
                        "proofs/SubtreeProofs/Paper2004/OrderedTree.lean")
        before, _ = tree_drawing(EXAMPLE_BRANCHING, anchor=(-3.8, 1.30), width=3.7, highlights=((0, 0),))
        after, _ = tree_drawing(EXAMPLE_REDUCED, anchor=(3.8, 1.30), width=3.7, highlights=((0, 0),))
        before_label = self.text_at("BEFORE", -3.8, 1.95, 21, MUTED)
        after_label = self.text_at("AFTER", 3.8, 1.95, 21, MUTED)
        arrow = Arrow([-1.35, .15, 0], [1.35, .15, 0], color=TEAL, buff=.05, stroke_width=5)
        self.play(FadeIn(before), FadeIn(before_label))
        self.beat()
        self.play(GrowArrow(arrow), FadeIn(after), FadeIn(after_label))
        # Render the relation as mathematics and its explanation as native text.
        # This also avoids \text in the formula that failed for one TeX setup.
        eq = MathTex(r"T'\preceq T", color=FG).scale(1.02)
        meaning = t("if and only if T' is reachable by edge contractions", 22, FG)
        description = VGroup(eq, meaning).arrange(DOWN, buff=.22).move_to([0, -1.77, 0])
        note = self.text_at("The root is retained; sibling order is preserved.", 0, -2.75, 22, MUTED)
        self.play(Write(eq), FadeIn(meaning), FadeIn(note))
        self.beat()


class BalancedWords(MathPresentation):
    """One matched pair per non-root vertex, exact round-trip encoding."""
    def construct(self):
        self.setup_page("A rooted tree is a balanced word", "Lozano-Valiente / encoding",
                        "Mathlib DyckWord; Paper2004/EncodingEquivalence.lean")
        tree, positions = tree_drawing(EXAMPLE_BRANCHING, anchor=(-3.6, 1.15), width=3.9)
        word = encode_tree(EXAMPLE_BRANCHING)
        title = self.text_at("Depth-first traversal", 2.30, 1.40, 30, TEAL)
        symbols = VGroup(*[MathTex(symbol, color=TEAL if i in (0, 5) else FG).scale(1.55)
                           for i, symbol in enumerate(word)])
        symbols.arrange(RIGHT, buff=.32).move_to([2.35, .40, 0])
        braces = self.text_at("0 = descend        1 = return", 2.35, -.62, 23, MUTED)
        cursor = Circle(radius=.36, color=AMBER, stroke_width=4).move_to(positions[()])
        self.play(Create(tree), FadeIn(title), FadeIn(braces), FadeIn(cursor))
        # Exact DFS edge events: descending writes 0, returning writes 1.
        events = ((0,), (0, 0), (0,), (0, 1), (0,), ())
        for target, glyph in zip(events, symbols):
            self.play(cursor.animate.move_to(positions[target]), FadeIn(glyph), run_time=.48)
        self.play(FadeOut(cursor))
        self.beat()
        split = MathTex(r"001011 = 0\,(01)(01)\,1", color=FG).scale(1.02).move_to([0, -1.66, 0])
        size = MathTex(r"\mathrm{semilength}(w)=|E(T)|=3", color=AMBER).scale(.86).move_to([0, -2.55, 0])
        self.play(Write(split), Write(size))
        self.beat()


class DeletionIsContraction(MathPresentation):
    def construct(self):
        self.setup_page("Deleting a matched pair contracts an edge", "The structural bridge",
                        "Paper2004/ContractionSoundness.lean; ContractionCompleteness.lean")
        a = MathTex(r"0\,0\,1\,0\,1\,1", color=FG).scale(1.5).move_to([0, 1.15, 0])
        b = MathTex(r"0\,0\,1\,1", color=TEAL).scale(1.5).move_to([0, -.34, 0])
        self.play(Write(a))
        self.beat()
        self.play(Write(b), FadeIn(self.text_at("delete one matched 01 pair", 3.2, .28, 22, AMBER)))
        iff = MathTex(r"T'\preceq T\iff\operatorname{enc}(T')"
                      r"\preceq_{\rm pair}\operatorname{enc}(T)", color=FG).scale(.91)
        iff.move_to([0, -1.95, 0])
        self.play(Write(iff))
        caveat = self.text_at("The paper's literal printed containment relation differs.", 0, -2.85, 21, ROSE)
        self.play(FadeIn(caveat))
        self.beat()


class OrderedRecurrence(MathPresentation):
    """This is exactly the operational three-branch recurrence in DynamicProgram.lean."""
    def construct(self):
        self.setup_page("The three-way dynamic program", "Lozano-Valiente / Lemma 8",
                        "proofs/SubtreeProofs/Paper2004/DynamicProgram.lean")
        decomposition = MathTex(r"a=0x1y,\qquad b=0u1v", color=FG).scale(.95).move_to([0, 1.77, 0])
        self.play(Write(decomposition))
        self.beat()
        cases = [
            (TEAL, r"1 + L(x,u) + L(y,v)", "keep the first matched pairs"),
            (AMBER, r"L(x+y,b)", "contract the first edge in a"),
            (ROSE, r"L(a,u+v)", "contract the first edge in b"),
        ]
        for i, (color, formula, explain) in enumerate(cases):
            y = .85 - i * 1.18
            bg = panel(11.5, .99).move_to([0, y, 0])
            f = MathTex(formula, color=color).scale(.82).move_to([-2.65, y, 0])
            note = t(explain, 23, MUTED).move_to([2.4, y, 0])
            self.play(FadeIn(bg), Write(f), FadeIn(note), run_time=.8)
            self.beat(.25)
        bottom = MathTex(r"L(a,b)=\max\{\text{these three candidates}\}", color=FG)
        bottom.scale(.85).move_to([0, -2.93, 0])
        self.play(Write(bottom))
        self.beat()


class CorrectnessAndComplexity(MathPresentation):
    def construct(self):
        self.setup_page("What the proof must establish", "Independent specification first",
                        "Paper2004/DynamicProgram.lean; Decomposition.lean; TreeStateBounds.lean")
        target = MathTex(r"\mathrm{OPT}(a,b)="
                         r"\max\{\lvert s\rvert:\ s\preceq a,\ s\preceq b\}", color=FG)
        target.scale(.95).move_to([0, 1.55, 0])
        self.play(Write(target))
        self.beat()
        rows = [
            ("SEMANTICS", "pair deletion  <->  tree edge contraction", TEAL),
            ("SOUNDNESS", "every DP witness is a common embedding", BLUE),
            ("OPTIMALITY", "every feasible witness is bounded by the DP", AMBER),
            ("COMPLEXITY", "count states, transitions, and implementation costs", ROSE),
        ]
        for i, (title, desc, color) in enumerate(rows):
            y = .55 - i*.89
            b = panel(11.7, .75).move_to([0, y, 0])
            label = t(title, 20, color).move_to([-4.25, y, 0])
            detail = t(desc, 21, FG).move_to([1.0, y, 0])
            self.play(FadeIn(b), FadeIn(label), FadeIn(detail), run_time=.5)
        target_bound = MathTex(
            r"O\!\left(n_1n_2\min(d_1,\ell_1)\min(d_2,\ell_2)\right)",
            color=AMBER).scale(.74).move_to([0, -3.04, 0])
        self.play(Write(target_bound))
        self.beat()


class AffinityExtensions(MathPresentation):
    def construct(self):
        self.setup_page("Extensions: node affinities and witnesses", "Beyond the 2004 unweighted problem",
                        "balanced_embedding.py; balanced_isomorphism.py; Cython variants")
        equation = MathTex(r"\operatorname{score}(M)=\sum_{(u,v)\in M} a(u,v)", color=FG)
        equation.scale(1.03).move_to([0, 1.35, 0])
        self.play(Write(equation))
        descriptions = [
            "Compatibility may be equality, a predicate, or a score.",
            "Embedding and isomorphism are different feasible sets.",
            "Witnesses must map back to original input vertices.",
            "The Cython implementation informs intent; it may contain bugs.",
        ]
        for i, item in enumerate(descriptions):
            line = t(item, 24, FG if i < 3 else AMBER)
            line.move_to([0, .40 - .72*i, 0])
            self.play(FadeIn(line, shift=LEFT*.2), run_time=.55)
        self.beat()


class WeightedUnorderedMatching(MathPresentation):
    def construct(self):
        self.setup_page("Unordered children become a matching problem", "Droschinsky 2016",
                        "MFCS 2016, Eq. (1); Droschinsky2016/RootedRecurrence.lean")
        formula = MathTex(
            r"F(u,v)=w_V(u,v)+\max_{M\;\mathrm{matching}}"
            r"\sum_{(a,b)\in M}\big(w_E(ua,vb)+F(a,b)\big)", color=FG)
        formula.scale(.70).move_to([0, 1.83, 0])
        matrix = weight_matrix(EXAMPLE_MATCHING, selected=(), x=0, y=.45, size=1.15)
        left = t("2 children", 25, BLUE).move_to([-3.5, .15, 0])
        right = t("3 children", 25, AMBER).move_to([3.5, .15, 0])
        self.play(Write(formula), FadeIn(matrix), FadeIn(left), FadeIn(right))
        self.beat()
        score, pairs = max_weight_partial_matching(EXAMPLE_MATCHING)
        selected_boxes = VGroup(*(SurroundingRectangle(matrix[r * 3 + c], color=TEAL, buff=.07)
                                  for r, c in pairs))
        self.play(*(Create(frame) for frame in selected_boxes), run_time=.9)
        result = MathTex(r"8 + 7 = " + str(score), color=TEAL).scale(1.12)
        result.move_to([0, -2.23, 0])
        note = self.text_at("Unmatched children are allowed. Reordering is allowed.", 0, -2.95, 21, MUTED)
        self.play(Write(result), FadeIn(note))
        self.beat()


class SparseMatchingOptimization(MathPresentation):
    def construct(self):
        self.setup_page("Reuse structure across matching subproblems", "Droschinsky 2016 / optimization",
                        "MFCS 2016, O(n^2 Delta) algorithm; distinct from a generic Hungarian loop")
        base = panel(3.4, 2.0).move_to([-4.3, .55, 0])
        sub = panel(3.4, 2.0).move_to([0, .55, 0])
        warm = panel(3.4, 2.0).move_to([4.3, .55, 0])
        self.play(FadeIn(base), FadeIn(sub), FadeIn(warm))
        self.play(Write(self.text_at("matching for (u,v)", -4.3, .55, 22)),
                  Write(self.text_at("related subproblem", 0, .55, 22)),
                  Write(self.text_at("reuse matching state", 4.3, .55, 22)))
        arrows = [Arrow([-2.55, .55, 0], [-1.80, .55, 0], color=TEAL, buff=.05),
                  Arrow([1.80, .55, 0], [2.55, .55, 0], color=TEAL, buff=.05)]
        self.play(*(GrowArrow(a) for a in arrows))
        self.beat()
        rate = MathTex(r"O(n^2\Delta)", color=AMBER).scale(1.75).move_to([0, -1.66, 0])
        explain = self.text_at("Published 2016 bound; not implied by calling Hungarian repeatedly.",
                               0, -2.76, 21, MUTED)
        self.play(Write(rate), FadeIn(explain))
        self.beat()


class TopologicalDistancePenalties(MathPresentation):
    def construct(self):
        self.setup_page("Skip vertices, but score paths correctly", "Droschinsky 2018 / Definition 4",
                        "MFCS 2018; Droschinsky2018/Specification.lean")
        one = node("A", node("B"))
        two = node("A", node("X", node("B")))
        l, _ = tree_drawing(one, anchor=(-3.7, 1.12), width=2.5, highlights=((0,),))
        r, _ = tree_drawing(two, anchor=(3.7, 1.32), width=2.5, dim=((0,),))
        self.play(FadeIn(l), FadeIn(r))
        direct = self.text_at("length 1", -3.7, 1.85, 22, TEAL)
        skipped = self.text_at("length 2; skip X", 3.7, 1.85, 22, AMBER)
        self.play(FadeIn(direct), FadeIn(skipped))
        self.beat()
        equation = MathTex(r"2\,\mathrm{node\ rewards}-0.25\,\mathrm{skip\ penalty}=1.75",
                           color=FG).scale(.83).move_to([0, -1.90, 0])
        warning = self.text_at("No direct-edge reward when either mapped path is longer than one edge.",
                               0, -2.76, 20, ROSE)
        self.play(Write(equation), FadeIn(warning))
        self.beat()


class MappedAndSkippedStates(MathPresentation):
    """The actual two-state rooted reference recurrence from the Lean development."""
    def construct(self):
        self.setup_page("Two DP states: mapped and skipped", "Droschinsky 2018 / rooted recurrence",
                        "Droschinsky2018/RootedDynamicProgram.lean; SkippedRecurrence.lean")
        labels = [
            (TEAL, "M(u,v)", "Map both endpoints", r"w_V(u,v)+\mathrm{MWM}(C_{u,v})"),
            (AMBER, "S(u,v)", "Skip an intermediate vertex", r"-p+\max\{M,S\}\text{ on adjacent states}"),
        ]
        for idx, (accent, symbol, explanation, formula) in enumerate(labels):
            yy = 1.27 - idx * 1.85
            bg = panel(11.7, 1.53).move_to([0, yy, 0])
            name = MathTex(symbol, color=accent).scale(1.10).move_to([-4.45, yy+.15, 0])
            desc = t(explanation, 22, MUTED).move_to([.6, yy+.38, 0])
            expr = MathTex(formula, color=FG).scale(.73).move_to([1.3, yy-.34, 0])
            self.play(FadeIn(bg), Write(name), FadeIn(desc), Write(expr))
            self.beat(.3)
        branch = MathTex(
            r"C_{u,v}(c,d)=\max\big\{w_E(uc,vd)+M(c,d),\ S(c,d)\big\}",
            color=FG).scale(.76).move_to([0, -2.28, 0])
        self.play(Write(branch))
        note = self.text_at("The displayed evaluator is correct but uses exhaustive child matching.",
                            0, -3.08, 19, MUTED)
        self.play(FadeIn(note))
        self.beat()


class ProofBoundary(MathPresentation):
    def construct(self):
        self.setup_page("From mathematics to executable guarantees", "Lean / Aeneas / Rust",
                        "proofs/PROOF_STATUS.md; verified Rust crates")
        stages = [
            ("SPECIFICATION", "Independent feasible mappings", TEAL),
            ("RECURRENCE", "Mathematical optimality", BLUE),
            ("RUST REFINEMENT", "Source translated by Aeneas", AMBER),
            ("PERFORMANCE", "Asymptotic and measured costs", ROSE),
        ]
        objects = []
        for i, (heading, description, color) in enumerate(stages):
            x = -4.7 + i*3.12
            box = panel(2.9, 2.2).move_to([x, .4, 0])
            main = t(heading, 19, color).move_to([x, .91, 0])
            lines = t(description, 18, FG).move_to([x, .07, 0])
            objects.append(VGroup(box, main, lines))
        self.play(*(FadeIn(o) for o in objects), run_time=1.5)
        self.beat()
        note = self.text_at("Proving a reference recurrence does not prove an optimized Python wheel.",
                            0, -1.90, 23, AMBER)
        self.play(FadeIn(note))
        self.beat()


class ApplicationExperiment(MathPresentation):
    def construct(self):
        self.setup_page("Candidate application: structural code comparison", "A falsifiable study",
                        "Tree-sitter; APTED; GumTree; RefactoringMiner; see RESEARCH_AGENDA.md")
        cols = [
            ("INPUT", "Code versions\nparse to AST", TEAL),
            ("MAPPING", "Ordered embedding\nnode affinities", BLUE),
            ("BASELINES", "APTED / GumTree\nRefactoringMiner", AMBER),
            ("OUTCOMES", "mapping quality\nlatency / memory", ROSE),
        ]
        self.play(*(FadeIn(card(title, body, color, width=2.92, height=2.45).move_to([-4.68 + 3.12*i, .60, 0]))
                    for i, (title, body, color) in enumerate(cols)), run_time=1.3)
        self.beat()
        caveat = self.text_at("Different objectives: compare on a shared downstream task, not raw scores.",
                              0, -1.75, 22, FG)
        self.play(FadeIn(caveat))
        bottom = self.text_at("Hypothesis to test, not an established empirical advantage.",
                              0, -2.75, 20, MUTED)
        self.play(FadeIn(bottom))
        self.beat()


class PaperContribution(MathPresentation):
    def construct(self):
        self.setup_page("What could justify a new paper?", "Research contribution, not reproduction",
                        "Original papers: Lozano-Valiente 2004; Droschinsky et al. 2016/2018")
        lines = [
            (TEAL, "Formal verification of source-level optimized implementations"),
            (BLUE, "Validated extensions: affinities, witnesses, robust APIs"),
            (AMBER, "Reproducible performance vs. strong native baselines"),
            (ROSE, "Measurable improvement on an application benchmark"),
        ]
        for i, (color, text) in enumerate(lines):
            y = 1.60 - .89*i
            bg = panel(11.5, .71).move_to([0, y, 0])
            label = t(text, 23, color).move_to([0, y, 0])
            self.play(FadeIn(bg), FadeIn(label), run_time=.55)
        self.beat()
        foot = self.text_at("New theorem, implementation, or empirical evidence must be clearly separated.",
                            0, -2.65, 19, MUTED)
        self.play(FadeIn(foot))
        self.beat()


SCENES = [
    AllProblems, OrderedContraction, BalancedWords, DeletionIsContraction,
    OrderedRecurrence, CorrectnessAndComplexity, AffinityExtensions,
    WeightedUnorderedMatching, SparseMatchingOptimization,
    TopologicalDistancePenalties, MappedAndSkippedStates, ProofBoundary, ApplicationExperiment,
    PaperContribution,
]
