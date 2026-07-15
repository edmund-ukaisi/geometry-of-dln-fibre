## Verdict: [NEEDS-AOYAGI]

[FACT] From S1–S4 plus the Nat gate alone, the desired lower bound does **not** follow. The missing ingredient is control of fractional—not merely ordinary—codimension.

[FACT] Allowing Aoyagi, the bound follows immediately. Writing \(m=\mathrm{minAdm}\) and \(T=m-ab\),

\[
\operatorname{rlct}_x(K)\ge \operatorname{rlct}_{\mathrm{global}}(K)
=\frac m2\ge \frac T2.
\]

Thus no actual DLN point can violate the requested bound. What remains unresolved is a native proof from the atlas.

The proposed dichotomy is therefore false: failure of the stated native argument does not imply existence of a DLN deficit point.

### Q1: the cyclic obstruction

[FACT] For

\[
G=e_1^2e_2^2+e_2^2e_3^2+e_3^2e_1^2,
\]

the Newton vertices are

\[
(2,2,0),\quad(0,2,2),\quad(2,0,2).
\]

Their average is \((4/3,4/3,4/3)\). Every Newton-polyhedron point has coordinate sum at least \(4\), so the diagonal first meets it at

\[
(t,t,t),\qquad t=\frac43.
\]

The principal polynomial is positive on \((\mathbb R^\times)^3\), hence real Newton-nondegenerate, and

\[
\operatorname{rlct}(G)=\frac1t=\frac34.
\]

Its zero set is the union of the three coordinate axes, of codimension \(2\), so

\[
\frac{\operatorname{rlct}(G)}{\operatorname{codim}(G)/2}=\frac34.
\]

Thus multilinearity and exponent \(\le2\) do **not** by themselves forbid deficits.

[FACT] No explicit DLN germ boundedly equivalent to this cyclic germ is currently supplied or implied by the premises. Producing one would refute the stated open local-equality conjecture. Proving that no DLN point has any deficit would prove that conjecture. Consequently, the requested “explicit DLN deficit or proof none exists” is precisely unresolved; neither answer can honestly be asserted from the established background.

### Q2: exact slack criterion

For a monomialized transverse chart of the form

\[
K_\perp\asymp \sum_{i=1}^{q}u_i^2+
 \sum_{E\in\mathcal H}\left(\prod_{j\in E}v_j\right)^2,
\]

let \(\tau(\mathcal H)\) be the integral vertex-cover number and \(\tau^*(\mathcal H)\) its fractional relaxation.

[FACT]

\[
C_{\mathrm{chart}}=q+\tau,\qquad
\operatorname{rlct}(K_\perp)=\frac{q+\tau^*}{2}.
\]

Hence

\[
\text{deficit}=\frac{C_{\mathrm{chart}}}{2}
-\operatorname{rlct}(K_\perp)
=\frac{\tau-\tau^*}{2}.
\]

The Nat gate proves only

\[
q+\tau\ge T.
\]

The desired native bound requires the stronger, fractional gate

\[
\boxed{q+\tau^*\ge T}.
\]

Equivalently, the slack absorbs the deficit exactly when

\[
\tau-\tau^*\le C_{\mathrm{chart}}-T.
\]

For the cyclic example, \((\tau,\tau^*)=(2,3/2)\): the RLCT deficit is \(1/4\). One unit of integer codimension slack absorbs one isolated cycle, but multiple or more complicated entanglements require an actual bound on the total integrality gap.

[FACT] The worst DLN deficit ratio is unknown. The local conjecture predicts it is \(1\). Aoyagi gives the nonnative bound

\[
\frac{\operatorname{rlct}_x}{\operatorname{codim}_x/2}
\ge \frac{m}{\operatorname{codim}_x}.
\]

Growth of \(C_k\) alone does not prove that its slack dominates: one must control \(\tau-\tau^*\).

### Q3: weaker, but not yet proved

[FACT] On a chart where \(C_{\mathrm{chart}}=\operatorname{codim}_x\),

\[
\operatorname{rlct}_{\mathrm{chart}}\ge \frac{C_{\mathrm{chart}}}{2}
\]

combined with Watanabe’s upper bound is exactly local equality.

By contrast,

\[
\operatorname{rlct}_{\mathrm{chart}}\ge\frac{T}{2},
\qquad T<C_{\mathrm{chart}},
\]

is genuinely weaker and permits a deficit up to

\[
\frac{C_{\mathrm{chart}}-T}{2}.
\]

So it may be easier than the open conjecture. But S1–S4 plus the integral Nat gate do not exploit that room; a fractional-Nat estimate is still missing.

### Q4: first entanglement

[FACT] “Morse–Bott at every two-layer point” is literally false. For scalar \(FE\),

\[
K(f,e)=f^2e^2
\]

at \((0,0)\) has zero set equal to two crossing axes and zero Hessian, so it is not Morse–Bott.

The substantive no-entanglement claim is correct: a two-factor Schur reduction leaves one residual multiplication block. Its monomial incidence is bipartite, where \(\tau=\tau^*\); no odd cyclic cover gap is possible.

For three layers, writing the base point as \((A,B,C)\),

\[
\begin{aligned}
(A+a)(B+b)(C+c)
={}&aBC+AbC+ABc\\
&+abC+aBc+Abc+abc ,
\end{aligned}
\]

since \(ABC=0\). After the linear terms are eliminated, the three pairwise terms

\[
abC,\qquad aBc,\qquad Abc
\]

can share variables in a triangle. Kernel alignments can make all three relevant while spectators lose rank. This is the first possible cyclic mechanism. Whether full DLN composition forces extra transverse terms that destroy the deficit is exactly the unresolved structural issue. Scalar width-one chains cannot realize it.

### Cleanest native sufficient condition

Prove on every rank-profile chart either:

\[
K_\perp\gtrsim G,\qquad \operatorname{rlct}(G)\ge \frac{m-ab}{2},
\]

for an S1–S4-computable comparator \(G\); or, after Newton monomialization, prove the fractional Nat gate

\[
q+\tau^*(\mathcal H)\ge m-ab.
\]

This covers disjoint, acyclic, bipartite, and more generally balanced seam incidences, as well as entangled charts whose integrality gap fits inside the slack. It does **not** presently cover every in-scope entangled chart. That residual needs Aoyagi for a known proof, or a new fractional/resolution theorem—not the open local-equality conjecture itself.