from __future__ import annotations

from manim import *
import numpy as np


config.background_color = "#101216"


BG = "#101216"
PANEL = "#171B22"
FG = "#F4F0E8"
MUTED = "#B8C0CC"
BLUE = "#58A6FF"
GOLD = "#F4C542"
RED = "#FF6B6B"
GREEN = "#7DCE82"
CYAN = "#64D2FF"
PURPLE = "#C792EA"
WAIT_SCALE = 4.0


class CoreMachineryBarcode(Scene):
    def construct(self):
        self.caption_box = Rectangle(width=13.4, height=1.08)
        self.caption_box.set_fill(PANEL, opacity=0.82)
        self.caption_box.set_stroke("#2B3240", width=1)
        self.caption_box.to_edge(DOWN, buff=0.22)
        self.add(self.caption_box)
        self.current_caption = VGroup()

        self.opening()
        self.multiplication_map()
        self.rank_pattern()
        self.base_change()
        self.interval_module()
        self.gabriel_decomposition()
        self.ranks_count_bars()
        self.inclusion_exclusion()
        self.running_example()
        self.classification_close()

    def caption(self, *lines: str, wait: float = 0.0):
        new_caption = VGroup()
        for line in lines:
            new_caption.add(Text(line, font_size=25, color=FG))
        new_caption.arrange(DOWN, aligned_edge=LEFT, buff=0.10)
        new_caption.move_to(self.caption_box.get_center())
        new_caption.align_to(self.caption_box, LEFT).shift(RIGHT * 0.45)
        if self.current_caption:
            self.play(FadeOut(self.current_caption, shift=DOWN * 0.1), run_time=0.25)
        self.current_caption = new_caption
        self.play(FadeIn(new_caption, shift=UP * 0.1), run_time=0.35)
        if wait:
            self.wait(wait * WAIT_SCALE)

    def clear_group(self, group: Mobject, run_time: float = 0.7):
        self.play(FadeOut(group), run_time=run_time)

    def formula(self, tex: str, font_size: int = 42, color: str = FG) -> MathTex:
        return MathTex(tex, font_size=font_size, color=color)

    def make_space(self, label: str, dim: int, x: float, y: float = 0.75) -> VGroup:
        rect = Rectangle(width=0.92, height=2.35)
        rect.set_fill("#16202D", opacity=0.85)
        rect.set_stroke(BLUE, width=2)
        rect.move_to([x, y, 0])

        dots = VGroup()
        offsets = np.linspace(0.58, -0.58, max(dim, 1))
        for n, off in enumerate(offsets[:dim]):
            dot = Dot([x, y + off, 0], radius=0.055, color=GOLD if n == 0 else CYAN)
            dots.add(dot)

        label_tex = MathTex(label, font_size=32, color=FG).next_to(rect, UP, buff=0.16)
        dim_tex = Text(f"dim {dim}", font_size=16, color=MUTED).next_to(rect, DOWN, buff=0.13)
        return VGroup(rect, dots, label_tex, dim_tex)

    def make_chain(self, labels, dims, y: float = 0.75, width: float = 10.6):
        n = len(labels)
        xs = np.linspace(-width / 2, width / 2, n)
        spaces = VGroup(*[self.make_space(labels[i], dims[i], xs[i], y) for i in range(n)])
        arrows = VGroup()
        for i in range(n - 1):
            start = spaces[i][0].get_right() + RIGHT * 0.08
            end = spaces[i + 1][0].get_left() + LEFT * 0.08
            arrow = Arrow(start, end, buff=0.0, color=BLUE, stroke_width=4, max_tip_length_to_length_ratio=0.12)
            label = MathTex(f"A_{i + 1}", font_size=32, color=BLUE).next_to(arrow, UP, buff=0.12)
            arrows.add(VGroup(arrow, label))
        return spaces, arrows, xs

    def make_bar(self, xs, start: int, end: int, y: float, color: str = GREEN, label: str | None = None):
        line = Line([xs[start], y, 0], [xs[end], y, 0], color=color, stroke_width=9)
        left = Dot(line.get_start(), radius=0.075, color=color)
        right = Dot(line.get_end(), radius=0.075, color=color)
        group = VGroup(line, left, right)
        if label:
            tag = Text(label, font_size=20, color=color).next_to(line, RIGHT, buff=0.20)
            group.add(tag)
        return group

    def title(self, text: str, subtitle: str | None = None):
        title = Text(text, font_size=46, color=FG, weight=BOLD)
        if subtitle:
            sub = Text(subtitle, font_size=28, color=MUTED)
            return VGroup(title, sub).arrange(DOWN, buff=0.25)
        return title

    def opening(self):
        title = self.title("The Core Machinery", "A chain of matrices hides a barcode")
        title.move_to(UP * 1.45)
        spaces, arrows, xs = self.make_chain([r"k^{d_0}", r"k^{d_1}", r"k^{d_2}", r"k^{d_N}"], [2, 3, 2, 2], y=-0.55)
        dots = VGroup()
        for y in [0.25, -0.25]:
            dots.add(Dot([xs[0], -0.55 + y, 0], color=GOLD, radius=0.055))
        hidden_bar = self.make_bar(xs, 0, 3, -0.10, GOLD)

        group = VGroup(title, spaces, arrows, hidden_bar)
        self.play(FadeIn(title, shift=UP * 0.3), run_time=1.0)
        self.caption("A chain of matrices hides a finite barcode.", wait=2.3)
        self.play(LaggedStart(Create(spaces), Create(arrows), lag_ratio=0.2), run_time=2.0)
        self.play(Create(hidden_bar), run_time=1.2)
        self.caption("The video follows the hidden directions that survive through the chain.", wait=3.0)
        self.clear_group(group)

    def multiplication_map(self):
        spaces, arrows, xs = self.make_chain([r"k^{d_0}", r"k^{d_1}", r"k^{d_2}", r"k^{d_N}"], [2, 3, 2, 2], y=0.9)
        chain = VGroup(spaces, arrows)
        formula = self.formula(r"\operatorname{mult}(A_\ast)=A_N\cdots A_2A_1", 42)
        formula.next_to(chain, DOWN, buff=0.55)
        long_arrow = CurvedArrow(
            spaces[0][0].get_top() + UP * 0.25,
            spaces[-1][0].get_top() + UP * 0.25,
            angle=-TAU / 5,
            color=GOLD,
            stroke_width=5,
        )
        rank = self.formula(r"\operatorname{rank}(A_N\cdots A_1)=r_{0N}", 36, GOLD)
        rank.next_to(long_arrow, UP, buff=0.15)
        group = VGroup(chain, formula, long_arrow, rank)

        self.caption("Start with a fixed dimension vector and a composable chain.", wait=1.5)
        self.play(LaggedStart(Create(spaces), Create(arrows), lag_ratio=0.18), run_time=2.2)
        self.caption("The multiplication map keeps only the endpoint composition.", wait=1.5)
        self.play(Write(formula), run_time=1.1)
        self.play(Create(long_arrow), FadeIn(rank, shift=UP * 0.15), run_time=1.4)
        self.caption("That endpoint rank is important, but it is only one measurement.", wait=4.2)
        self.clear_group(group)

    def rank_pattern(self):
        spaces, arrows, xs = self.make_chain([r"V_0", r"V_1", r"V_2", r"V_3"], [2, 3, 2, 2], y=1.05)
        chain = VGroup(spaces, arrows)
        self.play(Create(chain), run_time=1.5)
        self.caption("Instead, measure every interval composition.", wait=1.5)

        intervals = VGroup()
        labels = VGroup()
        pairs = [(0, 1, 0.9), (1, 3, 1.45), (0, 3, 2.0)]
        for i, j, h in pairs:
            arr = CurvedArrow([xs[i], 1.25 + h, 0], [xs[j], 1.25 + h, 0], angle=-TAU / 6, color=GOLD, stroke_width=4)
            lab = MathTex(f"r_{{{i}{j}}}", font_size=32, color=GOLD).next_to(arr, UP, buff=0.05)
            intervals.add(arr)
            labels.add(lab)
        self.play(LaggedStart(*[Create(m) for m in intervals], lag_ratio=0.25), run_time=2.0)
        self.play(FadeIn(labels, shift=UP * 0.12), run_time=0.8)

        definition = self.formula(r"r_{ij}=\operatorname{rank}(A_jA_{j-1}\cdots A_{i+1}),\qquad r_{ii}=d_i", 34)
        definition.to_edge(UP, buff=0.28)
        self.play(Write(definition), run_time=1.1)
        self.caption("The rank pattern is the full survival table.", wait=2.4)

        table = self.rank_table(
            [["d_0", "r_{01}", "r_{02}", "r_{03}"],
             [None, "d_1", "r_{12}", "r_{13}"],
             [None, None, "d_2", "r_{23}"],
             [None, None, None, "d_3"]],
            cell=0.78,
            font_size=24,
        )
        table.scale(0.9)
        table.move_to(DOWN * 1.45)
        self.play(FadeIn(table, shift=UP * 0.25), run_time=1.2)
        self.caption("The corner entry is the product rank; the rest remembers the interior.", wait=4.2)
        self.clear_group(VGroup(chain, intervals, labels, definition, table))

    def rank_table(self, entries, cell: float = 0.75, font_size: int = 24):
        n = len(entries)
        cells = VGroup()
        for i in range(n):
            for j in range(n):
                value = entries[i][j]
                if value is None:
                    continue
                rect = Square(side_length=cell)
                rect.set_fill("#151A21", opacity=0.90)
                rect.set_stroke("#3A4352", width=1)
                rect.move_to([(j - (n - 1) / 2) * cell, ((n - 1) / 2 - i) * cell, 0])
                tex = MathTex(value, font_size=font_size, color=FG).move_to(rect.get_center())
                cells.add(VGroup(rect, tex))
        return cells

    def base_change(self):
        spaces, arrows, xs = self.make_chain([r"V_0", r"V_1", r"V_2", r"V_3"], [2, 3, 2, 2], y=0.75)
        chain = VGroup(spaces, arrows)
        self.play(Create(chain), run_time=1.6)
        self.caption("Now relabel coordinates independently at every vertex.", wait=1.4)

        ps = VGroup()
        for i, space in enumerate(spaces):
            p = MathTex(f"P_{i}", font_size=34, color=PURPLE).next_to(space[0], UP, buff=0.55)
            ps.add(p)
        self.play(LaggedStart(*[FadeIn(p, shift=DOWN * 0.2) for p in ps], lag_ratio=0.15), run_time=1.2)

        local = self.formula(r"(P\cdot A)_i=P_iA_iP_{i-1}^{-1}", 38, PURPLE)
        local.to_edge(UP, buff=0.32)
        self.play(Write(local), run_time=1.0)
        self.caption("This changes matrices, but not the intrinsic chain.", wait=2.0)

        telescoping = self.formula(
            r"(P\cdot A)_j\cdots(P\cdot A)_{i+1}=P_j(A_j\cdots A_{i+1})P_i^{-1}",
            32,
            GOLD,
        )
        telescoping.next_to(chain, DOWN, buff=0.55)
        self.play(TransformFromCopy(local, telescoping), run_time=1.2)

        brace = Brace(telescoping, DOWN, color=GOLD)
        invariant = Text("multiplication by invertibles preserves rank", font_size=24, color=GOLD)
        invariant.next_to(brace, DOWN, buff=0.10)
        self.play(GrowFromCenter(brace), FadeIn(invariant, shift=UP * 0.1), run_time=0.8)
        self.caption("So every interval rank is constant on a base-change orbit.", wait=4.0)
        self.clear_group(VGroup(chain, ps, local, telescoping, brace, invariant))

    def interval_module(self):
        xs = np.linspace(-5.0, 5.0, 5)
        vertices = VGroup()
        for i, x in enumerate(xs):
            dot = Dot([x, 0.55, 0], radius=0.09, color=BLUE)
            lab = MathTex(str(i), font_size=28, color=FG).next_to(dot, DOWN, buff=0.18)
            vertices.add(VGroup(dot, lab))
        edges = VGroup()
        for i in range(4):
            edges.add(Line(vertices[i][0].get_right(), vertices[i + 1][0].get_left(), color=BLUE, stroke_width=3))
        bar = self.make_bar(xs, 1, 3, 1.65, GREEN, r"$M_{13}$")
        zeros = VGroup(
            Text("0", font_size=30, color=MUTED).next_to(vertices[0][0], UP, buff=0.45),
            Text("0", font_size=30, color=MUTED).next_to(vertices[4][0], UP, buff=0.45),
        )
        ones = VGroup()
        for i in [1, 2, 3]:
            ones.add(MathTex("k", font_size=34, color=GREEN).next_to(vertices[i][0], UP, buff=0.45))
        formula = self.formula(r"M_{ij}:\hbox{ one }k\hbox{ on }[i,j],\quad 0\hbox{ outside}", 34)
        formula.to_edge(UP, buff=0.38)
        group = VGroup(vertices, edges, bar, zeros, ones, formula)

        self.play(Create(vertices), Create(edges), run_time=1.3)
        self.caption("The atomic object is one direction alive on a contiguous interval.", wait=1.5)
        self.play(Create(bar), FadeIn(ones, shift=UP * 0.15), FadeIn(zeros), run_time=1.4)
        self.play(Write(formula), run_time=1.0)
        self.caption("Inside the interval the arrows act as identity; outside it, the thread is absent.", wait=4.0)

        pulse = Dot([xs[1], 1.65, 0], color=GOLD, radius=0.10)
        self.play(FadeIn(pulse), run_time=0.2)
        self.play(MoveAlongPath(pulse, bar[0]), run_time=2.0, rate_func=linear)
        self.play(FadeOut(pulse), run_time=0.2)
        self.caption("Think of a bar as a one-dimensional thread with a birth and a death.", wait=3.0)
        self.clear_group(group)

    def gabriel_decomposition(self):
        xs = np.linspace(-4.6, 4.6, 4)
        labels = VGroup(*[MathTex(str(i), font_size=28, color=FG).move_to([xs[i], -1.95, 0]) for i in range(4)])
        guide = VGroup(*[Line([x, -1.60, 0], [x, 2.15, 0], color="#2D3542", stroke_width=1) for x in xs])
        bars = VGroup(
            self.make_bar(xs, 0, 3, 1.75, GREEN, "[0,3]"),
            self.make_bar(xs, 0, 1, 1.20, GOLD, "[0,1]"),
            self.make_bar(xs, 1, 2, 0.65, CYAN, "[1,2]"),
            self.make_bar(xs, 2, 3, 0.10, PURPLE, "[2,3]"),
            self.make_bar(xs, 3, 3, -0.45, RED, "[3,3]"),
        )
        theorem = self.formula(r"A_\ast\cong\bigoplus_{i\le j}M_{ij}^{\,m_{ij}}", 44)
        theorem.to_edge(UP, buff=0.35)
        group = VGroup(guide, labels, bars, theorem)

        self.caption("Gabriel's theorem says the whole chain splits into interval threads.", wait=1.5)
        self.play(Create(guide), FadeIn(labels), run_time=1.0)
        self.play(LaggedStart(*[Create(b) for b in bars], lag_ratio=0.18), run_time=3.0)
        self.play(Write(theorem), run_time=1.2)
        self.caption("The multiplicity m_ij is the number of bars born at i and dying at j.", wait=4.0)
        self.caption("For fixed dimensions, only finitely many such barcodes are possible.", wait=3.5)
        self.clear_group(group)

    def ranks_count_bars(self):
        xs = np.linspace(-4.8, 4.8, 4)
        guide = VGroup(*[Line([x, -1.55, 0], [x, 2.2, 0], color="#2D3542", stroke_width=1) for x in xs])
        labels = VGroup(*[MathTex(str(i), font_size=28, color=FG).move_to([xs[i], -1.90, 0]) for i in range(4)])
        bars = VGroup(
            self.make_bar(xs, 0, 0, 1.65, RED, "[0,0]"),
            self.make_bar(xs, 0, 1, 1.10, GOLD, "[0,1]"),
            self.make_bar(xs, 1, 3, 0.55, GREEN, "[1,3]"),
            self.make_bar(xs, 2, 3, 0.00, CYAN, "[2,3]"),
            self.make_bar(xs, 3, 3, -0.55, PURPLE, "[3,3]"),
        )
        group = VGroup(guide, labels, bars)
        self.play(Create(guide), FadeIn(labels), LaggedStart(*[Create(b) for b in bars], lag_ratio=0.13), run_time=2.6)
        self.caption("Ranks can be read directly from the barcode.", wait=1.3)

        bracket = BraceBetweenPoints([xs[1], -1.24, 0], [xs[2], -1.24, 0], DOWN, color=GOLD)
        bracket_label = MathTex(r"[i,j]=[1,2]", font_size=28, color=GOLD).next_to(bracket, DOWN, buff=0.10)
        self.play(GrowFromCenter(bracket), FadeIn(bracket_label), run_time=0.8)

        cover = VGroup(bars[2])
        self.play(Indicate(cover, color=GOLD, scale_factor=1.05), run_time=1.3)
        formula = self.formula(r"r_{ij}=\sum_{a\le i,\ b\ge j}m_{ab}", 42, GOLD)
        formula.to_edge(UP, buff=0.36)
        self.play(Write(formula), run_time=1.0)
        self.caption("The rank across [i,j] counts the bars that contain that whole interval.", wait=4.0)

        count = MathTex(r"r_{12}=1", font_size=44, color=GOLD).next_to(bracket_label, DOWN, buff=0.18)
        self.play(FadeIn(count, shift=UP * 0.1), run_time=0.6)
        self.caption("This is the cumulative transform from bar multiplicities to rank pattern.", wait=3.4)
        self.clear_group(VGroup(group, bracket, bracket_label, formula, count))

    def inclusion_exclusion(self):
        table = self.rank_table(
            [["r_{00}", "r_{01}", "r_{02}", "r_{03}"],
             [None, "r_{11}", "r_{12}", "r_{13}"],
             [None, None, "r_{22}", "r_{23}"],
             [None, None, None, "r_{33}"]],
            cell=0.82,
            font_size=24,
        )
        table.move_to(LEFT * 2.95 + UP * 0.65)
        formula = self.formula(r"m_{ij}=r_{ij}-r_{i,j+1}-r_{i-1,j}+r_{i-1,j+1}", 36, GOLD)
        formula.move_to(RIGHT * 2.1 + UP * 1.35)
        explanation = VGroup(
            Text("all bars covering [i,j]", font_size=23, color=FG),
            Text("- bars extending too far right", font_size=23, color=MUTED),
            Text("- bars starting too far left", font_size=23, color=MUTED),
            Text("+ bars subtracted twice", font_size=23, color=MUTED),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
        explanation.next_to(formula, DOWN, buff=0.45).align_to(formula, LEFT)
        stencil = VGroup(
            Rectangle(width=0.82, height=0.82).move_to(table[5][0].get_center()).set_stroke(GOLD, width=3),
            Rectangle(width=0.82, height=0.82).move_to(table[6][0].get_center()).set_stroke(RED, width=3),
            Rectangle(width=0.82, height=0.82).move_to(table[2][0].get_center()).set_stroke(RED, width=3),
            Rectangle(width=0.82, height=0.82).move_to(table[3][0].get_center()).set_stroke(GREEN, width=3),
        )
        group = VGroup(table, formula, explanation, stencil)

        self.play(FadeIn(table, shift=UP * 0.2), run_time=1.2)
        self.caption("Because ranks are cumulative counts, exact bars come from differences.", wait=1.8)
        self.play(Write(formula), run_time=1.2)
        self.play(LaggedStart(*[Create(s) for s in stencil], lag_ratio=0.18), run_time=1.2)
        self.play(FadeIn(explanation, shift=RIGHT * 0.2), run_time=0.8)
        self.caption("Inclusion-exclusion isolates bars born exactly at i and dying exactly at j.", wait=4.5)

        conclusion = self.formula(r"\text{same rank pattern}\quad\Longrightarrow\quad\text{same barcode}", 36, GREEN)
        conclusion.next_to(formula, DOWN, buff=1.75)
        self.play(Write(conclusion), run_time=1.0)
        self.caption("This is the uniqueness half of the barcode classification.", wait=3.6)
        self.clear_group(VGroup(group, conclusion))

    def running_example(self):
        title = Text("Running example: (2,2,2) and BA = 0", font_size=34, color=FG, weight=BOLD)
        title.to_edge(UP, buff=0.28)
        matrices = self.formula(
            r"A=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad B=\begin{pmatrix}0&0\\0&1\end{pmatrix}",
            34,
            FG,
        )
        matrices.next_to(title, DOWN, buff=0.25)
        spaces, arrows, xs = self.make_chain([r"k^2", r"k^2", r"k^2"], [2, 2, 2], y=0.10, width=7.4)
        arrows[0][1].become(MathTex("A", font_size=34, color=BLUE).next_to(arrows[0][0], UP, buff=0.12))
        arrows[1][1].become(MathTex("B", font_size=34, color=BLUE).next_to(arrows[1][0], UP, buff=0.12))
        group = VGroup(title, matrices, spaces, arrows)
        self.play(FadeIn(title), Write(matrices), run_time=1.3)
        self.play(Create(spaces), Create(arrows), run_time=1.5)
        self.caption("The product is zero, but neither map has to be zero.", wait=2.0)

        thread1 = VMobject(color=GOLD, stroke_width=6)
        thread1.set_points_smoothly([[xs[0], 0.40, 0], [xs[1], 0.40, 0], [xs[1] + 0.25, 0.16, 0]])
        thread2 = VMobject(color=RED, stroke_width=6)
        thread2.set_points_smoothly([[xs[0], -0.40, 0], [xs[0] + 0.55, -0.64, 0]])
        thread3 = VMobject(color=GREEN, stroke_width=6)
        thread3.set_points_smoothly([[xs[1], -0.40, 0], [xs[2], -0.40, 0]])
        singleton = Dot([xs[2], 0.40, 0], radius=0.08, color=CYAN)
        threads = VGroup(thread1, thread2, thread3, singleton)
        self.play(Create(thread2), run_time=0.8)
        self.caption("One direction at vertex 0 is killed immediately: a bar [0,0].", wait=2.3)
        self.play(Create(thread1), run_time=1.0)
        self.caption("Another survives to vertex 1, then dies: a bar [0,1].", wait=2.3)
        self.play(Create(thread3), FadeIn(singleton), run_time=1.1)
        self.caption("A new middle direction survives to vertex 2, and one direction is born at vertex 2.", wait=2.6)

        self.play(FadeOut(threads), run_time=0.5)
        bars_x = np.linspace(-3.7, 3.7, 3)
        guide = VGroup(*[Line([x, -2.00, 0], [x, -0.35, 0], color="#2D3542", stroke_width=1) for x in bars_x])
        bar_labels = VGroup(*[MathTex(str(i), font_size=24, color=FG).move_to([bars_x[i], -2.2, 0]) for i in range(3)])
        bars = VGroup(
            self.make_bar(bars_x, 0, 0, -0.55, RED, "[0,0]"),
            self.make_bar(bars_x, 0, 1, -0.95, GOLD, "[0,1]"),
            self.make_bar(bars_x, 1, 2, -1.35, GREEN, "[1,2]"),
            self.make_bar(bars_x, 2, 2, -1.75, CYAN, "[2,2]"),
        )
        self.play(Create(guide), FadeIn(bar_labels), LaggedStart(*[Create(b) for b in bars], lag_ratio=0.18), run_time=2.1)
        self.caption("So the tuple is M_00 plus M_01 plus M_12 plus M_22.", wait=2.8)

        rank = self.rank_table(
            [["2", "1", "0"],
             [None, "2", "1"],
             [None, None, "2"]],
            cell=0.70,
            font_size=28,
        )
        rank.move_to(RIGHT * 4.65 + DOWN * 0.98)
        rank_title = MathTex(r"r_{ij}", font_size=30, color=FG).next_to(rank, UP, buff=0.16)
        self.play(FadeIn(rank_title), FadeIn(rank, shift=LEFT * 0.2), run_time=1.0)
        self.caption("The corner r_02 is zero because no bar crosses from 0 all the way to 2.", wait=4.2)

        incidence = self.formula(r"BA=0\quad\Longleftrightarrow\quad \operatorname{im}A\subseteq\ker B", 34, GOLD)
        incidence.move_to(UP * 2.25)
        self.play(Transform(matrices, incidence), run_time=1.0)
        self.caption("Geometrically, the image line of A lands inside the kernel line of B.", wait=4.5)
        self.clear_group(VGroup(group, guide, bar_labels, bars, rank, rank_title))

    def classification_close(self):
        title = Text("The classification", font_size=38, color=FG, weight=BOLD)
        title.to_edge(UP, buff=0.35)
        axes = VGroup(
            Arrow(LEFT * 3.7 + DOWN * 1.7, RIGHT * 3.9 + DOWN * 1.7, color=MUTED, stroke_width=3),
            Arrow(LEFT * 3.55 + DOWN * 1.85, LEFT * 3.55 + UP * 2.15, color=MUTED, stroke_width=3),
        )
        xlab = MathTex(r"r_{01}", font_size=28, color=MUTED).next_to(axes[0], RIGHT, buff=0.12)
        ylab = MathTex(r"r_{12}", font_size=28, color=MUTED).next_to(axes[1], UP, buff=0.12)
        pts_data = [
            ((0, 0), "A=B=0", RED),
            ((0, 1), "A=0, rk B=1", GOLD),
            ((0, 2), "A=0", GREEN),
            ((1, 0), "rk A=1, B=0", GOLD),
            ((1, 1), "rank-one incidence", CYAN),
            ((2, 0), "B=0", GREEN),
        ]
        points = VGroup()
        for (a, b), label, color in pts_data:
            pos = np.array([-3.2 + a * 2.2, -1.35 + b * 1.45, 0])
            dot = Dot(pos, radius=0.10, color=color)
            tag = MathTex(f"({a},{b})", font_size=23, color=color).next_to(dot, UP, buff=0.10)
            txt = Text(label, font_size=17, color=MUTED).next_to(dot, RIGHT, buff=0.12)
            points.add(VGroup(dot, tag, txt))

        condition = MathTex(r"r_{02}=0\quad\text{ means no full-length bar }[0,2]", font_size=34, color=GOLD)
        condition.next_to(title, DOWN, buff=0.35)
        slogan = MathTex(
            r"\text{orbits}\quad\Longleftrightarrow\quad\text{rank patterns}\quad\Longleftrightarrow\quad\text{barcodes}",
            font_size=40,
            color=GREEN,
        )
        slogan.to_edge(DOWN, buff=1.45)
        group = VGroup(title, axes, xlab, ylab, points, condition, slogan)

        self.play(FadeIn(title), Write(condition), run_time=1.1)
        self.caption("The zero-product locus is a finite union of rank-pattern orbits.", wait=1.8)
        self.play(Create(axes), FadeIn(xlab), FadeIn(ylab), run_time=0.9)
        self.play(LaggedStart(*[FadeIn(p, scale=0.8) for p in points], lag_ratio=0.12), run_time=2.2)
        self.caption("For (2,2,2), the condition BA = 0 leaves exactly six orbits.", wait=3.4)
        self.play(Write(slogan), run_time=1.2)
        self.caption("For fixed dimensions, these are equivalent finite records.", wait=4.2)

        final = Text("The hidden barcode makes the geometry finite.", font_size=34, color=FG)
        final.move_to(UP * 0.20)
        self.play(FadeOut(VGroup(axes, xlab, ylab, points, condition)), Transform(title, final), run_time=1.1)
        self.caption("Next questions, such as components and codimensions, build on this classification.", wait=4.0)
        self.play(FadeOut(VGroup(title, slogan, self.current_caption, self.caption_box)), run_time=1.0)
