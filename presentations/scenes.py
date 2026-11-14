"""Animated mathematical presentation: Lozano-Valiente and Droschinsky.

Render: manim -qh presentations/scenes.py AllProblems (or ./presentations/render.py)
Optional interactive mode: pip install manim-slides; render with manim-slides.
No binary assets or repository implementations are required to render.
"""
from __future__ import annotations

from pathlib import Path
import os

from manim import (
    VGroup, Text, MathTex as ManimMathTex, TexTemplate, FadeIn, FadeOut, Create, Write,
    Transform, TransformMatchingTex, ReplacementTransform, GrowArrow,
    Arrow, Line, Rectangle, RoundedRectangle, SurroundingRectangle, Circle,
    DashedLine, RIGHT, LEFT, UP, DOWN, ORIGIN, WHITE, config,
)

from manim_slides import Slide

from narration import notes_for

from math_examples import (
    EXAMPLE_BRANCHING, EXAMPLE_REDUCED, EXAMPLE_SPLICED, EXAMPLE_MATCHING,
    node, encode_tree, lozano_dp_word, max_weight_partial_matching,
    path_contribution, lozano_recurrence_candidate_scores,
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


# All scenes are native click-advanced Manim Slides.
# All page layouts target the default Manim 16:9 frame (14.222 x 8 units).


class MathPresentation(Slide):
    """Each chapter is a real Manim Slides scene, with notes and build pauses.

    This mirrors the DKPS DeckSlide pattern: start the first build with
    next_slide(notes=...), advance *before* each following build, and finish
    with a short hold so the last animation's terminal frame is captured.
    """
    wait_time_between_slides = .12
    skip_reversing = True

    def __init__(self, *args, **kwargs):
        # Equivalent to the DKPS per-deck output_folder: scene metadata is
        # separate from ordinary Manim videos and from any older HTML viewer.
        kwargs.setdefault("output_folder", Path("slides-" + os.environ.get("SUBTREE_PRESENTATION_SLUG", "common-subtree-mathematics")))
        super().__init__(*args, **kwargs)

    def finish(self):
        # Reject off-screen labels before a broken build is published to HTML.
        # We inspect whole text objects rather than their individual SVG glyphs.
        limit_x = config.frame_width / 2 - .28
        limit_y = config.frame_height / 2 - .10
        def check(mob):
            if isinstance(mob, (Text, ManimMathTex)):
                if (mob.get_left()[0] < -limit_x or mob.get_right()[0] > limit_x
                        or mob.get_bottom()[1] < -limit_y
                        or mob.get_top()[1] > limit_y):
                    raise ValueError(
                        f"Text extends outside slide ({type(self).__name__}): "
                        f"{mob!r}. Reduce or reposition the label."
                    )
                return
            for sub in mob.submobjects:
                check(sub)
        for mob in self.mobjects:
            check(mob)
        self.wait(self.wait_time_between_slides)

    def setup_page(self, title, tag, source=""):
        config.background_color = BG
        # Keep the header on a single legible line: long chapter titles such as
        # "From mathematics to executable guarantees" used to extend beyond
        # the right edge. A fixed lower font size would shrink every title.
        heading = t(title, 41, FG)
        if heading.width > 12.20:
            heading.scale_to_fit_width(12.20)
        heading.to_edge(UP, buff=.45).align_to(LEFT * 6.40, LEFT)
        if heading.get_right()[0] > 6.41:
            raise ValueError(f"Heading crosses slide margin: {title!r}")
        section = t(tag.upper(), 18, TEAL)
        if section.width > 12.20:
            section.scale_to_fit_width(12.20)
        section.next_to(heading, DOWN, buff=.16).align_to(heading, LEFT)
        line = Line([-6.40, 2.42, 0], [6.40, 2.42, 0], color=PANEL_BORDER, stroke_width=2)
        if section.get_bottom()[1] <= line.get_y() + .08:
            raise ValueError(f"Header overlaps the content divider: {title!r}")
        source_line = t(source, 13, MUTED) if source else t("Common subtree mathematics", 13, MUTED)
        # Reserve the lower-right area for the PDF's page numbering.
        if source_line.width > 10.50:
            source_line.scale_to_fit_width(10.50)
        source_line.move_to([-.40, -3.72, 0])
        self.add(heading, section, line, source_line)
        # Follow the DKPS convention: the first build starts before drawing,
        # and carries the authored chapter narration as presenter notes.
        self.next_slide(notes=getattr(self, "intro_notes", None) or notes_for(type(self).__name__))

    def beat(self, seconds=1.0, *, notes=""):
        """Advance to the next mathematical step with optional presenter notes.

        The old numeric argument is retained for other scenes; slide advancement
        is manual, not time-driven. Presenter notes are never shown on the slide.
        """
        self.next_slide(notes=notes)

    def text_at(self, value, x, y, size=25, color=FG):
        text = t(value, size=size, color=color)
        # Text labels are positioned by center coordinates. Limit their width
        # to the space remaining inside the presentation frame.
        available = min(12.25, 2 * (6.45 - abs(x)))
        if text.width > available:
            text.scale_to_fit_width(available)
        return text.move_to([x, y, 0])


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
        self.finish()


class OrderedContraction(MathPresentation):
    """Click through a genuine internal-vertex contraction and child splicing."""
    def construct(self):
        self.setup_page("Ordered edge contraction", "Lozano-Valiente / semantics",
                        "proofs/SubtreeProofs/Paper2004/OrderedTree.lean")
        before, positions = tree_drawing(EXAMPLE_BRANCHING, anchor=(-3.8, 1.20), width=3.7)
        after, _ = tree_drawing(EXAMPLE_SPLICED, anchor=(3.8, 1.20), width=3.7)
        self.play(FadeIn(before), FadeIn(self.text_at("BEFORE", -3.8, 1.95, 21, MUTED)))
        self.beat(notes="The marked edge connects r to internal vertex a. Edge contraction removes a and retains its ordered descendants.")
        contracted = Line(positions[()], positions[(0,)], color=AMBER, stroke_width=10)
        chosen = self.text_at("Contract edge (r,a)", 0, 1.68, 24, AMBER)
        self.play(Create(contracted), FadeIn(chosen))
        self.beat(notes="The children b and c are spliced into the parent at the removed vertex position, preserving left-to-right order.")
        arrow = Arrow([-1.25, .18, 0], [1.25, .18, 0], color=TEAL, buff=.06, stroke_width=5)
        self.play(GrowArrow(arrow), FadeIn(after), FadeIn(self.text_at("AFTER", 3.8, 1.95, 21, MUTED)))
        self.beat(notes="This contraction deletes the pair enclosing the subtree a: 001011 becomes 0101. The number of edges drops from three to two.")
        relation = MathTex(r"001011\;\longrightarrow\;0101", color=FG).scale(1.08).move_to([0, -1.72, 0])
        explanation = self.text_at("Remove a; its ordered children b,c become children of r.", 0, -2.62, 22, FG)
        self.play(Write(relation), FadeIn(explanation))
        self.finish()

class BalancedWords(MathPresentation):
    """Every click advances one DFS edge event, then reveals the invariant."""
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
        # One press per traversal event. All glyphs are accurate to the
        # checked depth-first encoder (001011).
        events = ((0,), (0, 0), (0,), (0, 1), (0,), ())
        for target, glyph in zip(events, symbols):
            self.beat(notes="A depth-first edge traversal emits 0 when descending and 1 when returning. Each click reveals one symbol.")
            self.play(cursor.animate.move_to(positions[target]), FadeIn(glyph), run_time=.46)
        self.beat(notes="Every descent has a matching return. A tree with three non-root edges therefore has three matched pairs.")
        self.play(FadeOut(cursor))
        decomposition = MathTex(r"001011=0\,(01)(01)\,1", color=FG).scale(1.03).move_to([0, -1.62, 0])
        size = MathTex(r"\operatorname{semilength}(w)=|E(T)|=3", color=AMBER).scale(.83).move_to([0, -2.50, 0])
        self.play(Write(decomposition), Write(size))
        self.finish()

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
        self.finish()


class OrderedRecurrence(MathPresentation):
    """Show the mathematical choices and compute an exact small instance."""
    def construct(self):
        self.setup_page("The three-way dynamic program", "Lozano-Valiente / Lemma 8",
                        "proofs/SubtreeProofs/Paper2004/DynamicProgram.lean")
        decomposition = MathTex(r"a=0x1y,\qquad b=0u1v", color=FG).scale(.97).move_to([0, 1.85, 0])
        inputs = MathTex(r"a=001011,\quad b=0011", color=TEAL).scale(.86).move_to([0, 1.19, 0])
        self.play(Write(decomposition), Write(inputs))
        self.beat(notes="For a=001011 and b=0011, the first pair decompositions give x=0101, y empty, u=01, and v empty. We evaluate three candidates.")
        scores = lozano_recurrence_candidate_scores("001011", "0011")
        cases = [
            (TEAL, r"1+L(x,u)+L(y,v)", "keep matched pairs"),
            (AMBER, r"L(x+y,b)", "contract first edge of a"),
            (ROSE, r"L(a,u+v)", "contract first edge of b"),
        ]
        for i, ((color, formula, explain), value) in enumerate(zip(cases, scores)):
            y = .41 - i * .89
            backing = panel(11.8, .79).move_to([0, y, 0])
            f = MathTex(formula, color=color).scale(.74).move_to([-3.15, y, 0])
            note = t(explain, 19, MUTED).move_to([1.22, y, 0])
            value_mob = MathTex("="+str(value), color=color).scale(.94).move_to([5.08, y, 0])
            if i:
                self.beat(notes="Consider the next recurrence branch, obtained by contracting a first-edge alternative. Compare its score against the current best.")
            self.play(FadeIn(backing), Write(f), FadeIn(note), Write(value_mob))
        self.beat(notes="The matched-first-pair branch wins with score two; both contraction alternatives score one on this instance.")
        best = max(scores)
        conclusion = MathTex(r"L(001011,0011)=\max\{" + ",".join(map(str, scores)) + r"\}=" + str(best), color=FG)
        conclusion.scale(.83).move_to([0, -2.92, 0])
        self.play(Write(conclusion))
        self.finish()

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
        self.finish()


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
        self.finish()


class WeightedUnorderedMatching(MathPresentation):
    """A specific 2-by-3 matching and its chosen disjoint edges."""
    def construct(self):
        self.setup_page("Unordered children become a matching problem", "Droschinsky 2016",
                        "MFCS 2016, Eq. (1); Droschinsky2016/RootedRecurrence.lean")
        formula = MathTex(
            r"F(u,v)=w_V(u,v)+\max_{M\;\mathrm{matching}}"
            r"\sum_{(a,b)\in M}\left(w_E(ua,vb)+F(a,b)\right)", color=FG)
        formula.scale(.70).move_to([0, 1.83, 0])
        matrix = weight_matrix(EXAMPLE_MATCHING, selected=(), x=0, y=.42, size=1.15)
        self.play(Write(formula), FadeIn(matrix))
        self.beat(notes="The first matched child pair contributes weight eight. A matching cannot reuse either selected endpoint.")
        score, pairs = max_weight_partial_matching(EXAMPLE_MATCHING)
        for i, (row, col) in enumerate(pairs):
            if i:
                self.beat(notes="The second disjoint pair contributes seven. The remaining child on the right may stay unmatched.")
            frame = SurroundingRectangle(matrix[row * 3 + col], color=TEAL, buff=.07)
            self.play(Create(frame))
        self.beat(notes="The selected partial matching has weight fifteen, the maximum across disjoint child pairs.")
        result = MathTex(r"8+7=" + str(score), color=TEAL).scale(1.18).move_to([0, -2.23, 0])
        note = self.text_at("Each child is used at most once; the third is unmatched.", 0, -2.96, 20, MUTED)
        self.play(Write(result), FadeIn(note))
        self.finish()

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
        self.finish()


class TopologicalDistancePenalties(MathPresentation):
    """Contrast direct-edge reward with an extended-path penalty."""
    def construct(self):
        self.setup_page("Skip vertices, but score paths correctly", "Droschinsky 2018 / Definition 4",
                        "MFCS 2018; Droschinsky2018/Specification.lean")
        direct_tree = node("A", node("B"))
        extended_tree = node("A", node("X", node("B")))
        left, _ = tree_drawing(direct_tree, anchor=(-3.65, 1.12), width=2.5)
        right, _ = tree_drawing(extended_tree, anchor=(3.65, 1.32), width=2.5, dim=((0,),))
        self.play(FadeIn(left), FadeIn(right), FadeIn(self.text_at("One edge", -3.65, 1.93, 22, TEAL)),
                  FadeIn(self.text_at("Two-edge path via X", 3.65, 1.93, 22, AMBER)))
        self.beat(notes="When both mapped paths are direct edges, the edge reward of one point five is earned in addition to two node rewards.")
        edge_reward = path_contribution(1.5, 1, 1, .25)
        direct_score = MathTex(r"2\;\mathrm{(vertices)}+1.5\;\mathrm{(edge)}=" + f"{2+edge_reward:g}",
                               color=TEAL).scale(.82).move_to([0, -1.06, 0])
        self.play(Write(direct_score))
        self.beat(notes="If one endpoint path traverses an unmatched vertex, the direct-edge reward is absent. The skip penalty applies instead.")
        skipped_reward = path_contribution(1.5, 2, 1, .25)
        skipped_score = MathTex(r"2\;\mathrm{(vertices)}-0.25\;\mathrm{(skip)}=" + f"{2+skipped_reward:g}",
                                color=AMBER).scale(.82).move_to([0, -1.91, 0])
        self.play(Write(skipped_score))
        self.beat(notes="This is the 2018 scoring distinction that must be preserved in reference, optimized, and verified implementations.")
        warning = self.text_at("An extended path does not earn the direct-edge reward.", 0, -2.80, 21, ROSE)
        self.play(FadeIn(warning))
        self.finish()

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
        self.finish()


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
            main = t(heading, 19, color)
            lines = t(description, 18, FG)
            if main.width > 2.65:
                main.scale_to_fit_width(2.65)
            if lines.width > 2.65:
                lines.scale_to_fit_width(2.65)
            main.move_to([x, .91, 0])
            lines.move_to([x, .07, 0])
            objects.append(VGroup(box, main, lines))
        self.play(*(FadeIn(o) for o in objects), run_time=1.5)
        self.beat()
        note = self.text_at("Proving a reference recurrence does not prove an optimized Python wheel.",
                            0, -1.90, 23, AMBER)
        self.play(FadeIn(note))
        self.finish()


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
        self.finish()


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
        self.finish()


SCENES = [
    AllProblems, OrderedContraction, BalancedWords, DeletionIsContraction,
    OrderedRecurrence, CorrectnessAndComplexity, AffinityExtensions,
    WeightedUnorderedMatching, SparseMatchingOptimization,
    TopologicalDistancePenalties, MappedAndSkippedStates, ProofBoundary, ApplicationExperiment,
    PaperContribution,
]
