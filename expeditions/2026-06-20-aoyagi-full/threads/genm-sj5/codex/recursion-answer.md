## Q1 — recursion structure

**Verdict: a direct handoff to the undecorated one-shorter IH is not valid.**

After the peel, the integrand is weighted/decorated: the exceptional variable occurs both in the Jacobian and inside the deeper loss. The ordinary IH only controls

\[
\int F_{\mathrm{red}}^{-s},
\]

not

\[
\int G_{\mathrm{Gram/mono}}\,F_{\mathrm{red}}^{-s}
\]

with an unbounded, correlated weight \(G\).

At a binding cut, writing \(D=\minAdm(t,M_2,\ldots,M_L)\),

\[
c'-\frac{pq}{2}<\frac D2
\]

has arbitrarily little slack as \(c'\nearrow (pq+D)/2\). Hölder cannot repair this uniformly: an unbounded Gram weight has only finite \(L^\alpha\)-range, whereas approaching the sharp threshold would require \(\alpha\to\infty\).

Nor can \(\operatorname{diag}(b)\) be “absorbed by renaming” into the next free matrix. The substitution

\[
B\longmapsto \operatorname{diag}(b)B
\]

has Jacobian containing powers of the \(b_i\) and is singular when \(b_i=0\). That singular Jacobian is precisely the information the ledger records.

Thus the native architecture is:

- outer strong induction on chain length;
- inner induction on a decorated chart state carrying divisor support/sharing.

A stronger peel lemma may package the entire decorated resolution and return a genuinely shorter undecorated chain. Then the *outer driver* uses chain length alone, but the decorated inner argument has merely been encapsulated, not eliminated.

## Q2 — which atom?

**Verdict: ATOM-1 is not a valid native atom on the binding rank-deficient region. ATOM-2, interpreted as a joint in-box blow-up with a shared monomial ledger, is the native mechanism.**

If \(\operatorname{rank}Q_b=r<q\), the map

\[
\Gamma\longmapsto \Gamma Q_b
\]

has kernel dimension \(p(q-r)>0\). The full-space integrand is constant along those kernel directions, so the \(\mathbb R^{p\times q}\) integral is infinite. This is not merely a failure of the displayed determinant formula.

An exact scalar witness is

\[
B_c=\int_{[-1,1]^3}(x^2+y^2\gamma^2)^{-c}\,dx\,dy\,d\gamma.
\]

One computes \(B_c<\infty\) exactly for \(c<1\). But for \(c>1/2\),

\[
\int_{\mathbb R}(x^2+y^2\gamma^2)^{-c}\,d\gamma
 =K_c\,|y|^{-1}|x|^{1-2c},
\]

whose outer \(y\)-integral diverges. For \(c\le 1/2\), the full-space integral already diverges at infinity. Thus full-space enlargement can fail throughout the entire true box-finite range.

The full-rank identity can still be useful on a chart where \(\sigma_{\min}(Q_b)\) is bounded below. Merely knowing “full rank almost everywhere” is insufficient: the Gram majorant can diverge near the rank boundary even though the bounded integral remains finite.

A viable third mechanism is rank-adapted:

- on rank \(r\), integrate only the \(pr\) active \(\Gamma\)-directions;
- retain the \(p(q-r)\) kernel directions inside the box;
- recurse on the remaining corank.

That is effectively a rank/decorated version of Aoyagi’s resolution, not ATOM-1 as stated. Recursing on the Gram weight alone also requires a new Gram-decorated IH; the ordinary Frobenius-loss IH does not cover the joint weighted residual.

Two corrections to ATOM-2 as phrased:

1. Radialising \(\Gamma\) alone does not turn
   \(\|C_{\rm cross}+\Gamma Q_b\|^2\) into \(u_0^2(\cdots)\). The blow-up centre must include the compatible cross/divisor coordinates, followed by the unit Schur clears.

2. The radial integral does not “converge for \(c'>0\)” by itself. If the loss is \(u_0^2U\), it is

   \[
   \int_0^1u_0^{pq-1-2c'}\,du_0,
   \]

   finite iff \(c'<pq/2\). The larger sharp threshold arises only from the shared terminal monomial bookkeeping.

## Q3 — Gram threshold

Assume \(q\ge1\), all matrices in \(Y,A\) are free variables, and the tail widths are

\[
n_i=M_i,\qquad i=2,\ldots,L.
\]

Then

\[
\int \det(Q_bQ_b^\mathsf T)^{-a/2}<\infty
\quad\Longleftrightarrow\quad
a<\min_{2\le i\le L}(M_i-q+1),
\]

provided every \(M_i\ge q\). If some \(M_i<q\), then \(\operatorname{rank}Q_b<q\) identically, the ordinary Gram determinant is zero everywhere, and no positive \(a\) is integrable.

This follows exactly from Gaussian rotational invariance and Bartlett factorisation: each successive width \(n\) contributes a \(q\times n\) Wishart determinant whose negative \(a/2\)-moment is finite iff

\[
a<n-q+1.
\]

Thus the tightest tail width governs the answer. A free \(q\times n\) matrix has threshold \(n-q+1\), not “\(q\)” in general.

A contracting-tail example is \(q=2\), \(Y\in\mathbb R^{2\times2}\), \(A\in\mathbb R^{2\times5}\). Here

\[
\det(YAA^\mathsf TY^\mathsf T)
 =\det(Y)^2\det(AA^\mathsf T).
\]

The two thresholds are respectively \(1\) and \(4\), so the product threshold is \(1\), not the free final-\(Q\) value \(4\).

For ATOM-1’s actual exponent \(a=p\), the standalone Gram weight is integrable precisely when

\[
p<d-q+1,\qquad d=\min_{i\ge2}M_i,
\]

equivalently, for integers, \(p+q\le d\). Equality \(p=d-q+1\) is logarithmically divergent. Even when this marginal condition holds, it does not by itself control the correlated residual loss.

## Q4 — well-foundedness

For Aoyagi’s literal loop, \((S,J)\) alone is insufficient because Case 1(1) leaves both unchanged.

Let:

- \(R(S,J)\) be the number of pivot positions remaining in the finite ordered list of all legal layer/pivot states;
- \(E\) be the number of already-introduced exceptional labels with \(\widetilde t>J\).

Use the lexicographic measure

\[
(R(S,J),E)\in\mathbb N^2.
\]

Then:

- Case 1(1) lowers one selected label from \(J+J_1\) to \(J\), so \(R\) is fixed and \(E\) decreases;
- Case 1(2) and Case 2 advance \(J\), or complete the layer and advance \(S\), so \(R\) decreases regardless of what happens to \(E\).

This can be flattened to \((B+1)R+E\), where \(B\) bounds the finite label set. An equivalent implementation uses three coordinates: remaining labels, remaining stage budget, and above-pivot label count.

If a redesigned recursive call genuinely removes one matrix layer while carrying the decoration honestly, chain arity alone is enough for the outer induction. It does not prove termination of Aoyagi’s literal \((S,J)\) loop.

Finally, exact rank strata themselves have measure zero. “Binding deeper stratum” should mean the exceptional divisors obtained from neighbourhoods of those strata, not the integral over the bare set \(\{\operatorname{rank}Q_b\le q-2\}\).