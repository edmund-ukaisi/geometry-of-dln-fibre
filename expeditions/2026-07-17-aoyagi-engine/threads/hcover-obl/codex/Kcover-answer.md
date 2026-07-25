**VERDICT: CONDITIONAL GO** — symmetry transports chart-image covers exactly, but the current facts do not prove that one global \(\sigma\in G\) canonicalizes every pivot in the recursive history.

1. **Orbit coverage**

**Proved from the stated geometry:** If

\[
\forall w\in B_\rho\;\exists \sigma\in G:\ \sigma w\in C_{\rm can},
\]

then, since \(G\) contains inverses,

\[
w\in \sigma^{-1}(C_{\rm can})
\quad\Longrightarrow\quad
B_\rho\subseteq\bigcup_{\tau\in G}\tau(C_{\rm can}).
\]

**Not proved by root transitivity:** Moving the dominant root coordinate to the canonical position only places \(\sigma w\) in the root cone. Membership in \(C_{\rm can}\) imposes every subsequent pivot condition.

The missing induction must show that, after canonicalizing the first \(k\) pivots, their stabilizer:

- acts equivariantly on the next residual and center; and
- can move its next maximizing coordinate canonically without disturbing the previous \(k\) conditions.

Transitivity on individual positions does not imply transitivity on pivot histories. For example, \(S_n\) is transitive on positions but has different orbits on pairs such as \((i,i)\) and \((i,j)\). The depth-2 Schur check supports the induction but does not prove it at every node.

For the literal closed-ball containment, ties must also be included using weak argmax inequalities. “Up to a measure-zero tie locus” is not an exact cover.

2. **Transporting the cover**

For every canonical chart \(g_c:D_c\to W\),

\[
\operatorname{im}(\sigma\circ g_c)
   =\sigma(\operatorname{im}g_c)
\]

as an exact set identity. Moreover:

- \(D_c\) remains compact;
- \(\sigma\circ g_c\) is a.e. injective whenever \(g_c\) is;
- \(K\circ\sigma\circ g_c=K\circ g_c\);
- since \(D\sigma\) is a permutation matrix,
  \(\lvert\det D(\sigma\circ g_c)\rvert=\lvert\det Dg_c\rvert\).

Thus these are genuine transported resolution parametrizations. Ideal invariance alone would establish monomialization algebra, not any containment of target points in chart images.

3. **Most likely break**

The concrete failure point is replacing node-dependent permutations by one global permutation: each pivot may be individually canonicalizable, while no single \(\sigma\) simultaneously canonicalizes the entire recursive pivot history. A full-history equivariance/stabilizer induction is the required cover certificate.