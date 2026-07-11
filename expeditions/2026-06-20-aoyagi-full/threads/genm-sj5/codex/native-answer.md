### Q1 — ELEMENTARY [DERIVED]

The back-peel identity holds, assuming the banked identification of \(D(\rho)\) with the rank-shift `cCodim`.

Let \(S_r=\{\operatorname{rank}Z_{\mathrm{deep}}=r\}\), and write \(\delta_r=\operatorname{codim}S_r\). Over \(S_r\), the condition
\[
A_{\mathrm{piv}}Z_{\mathrm{deep}}=0
\]
imposes exactly \(tr\) independent linear conditions: each of the \(t\) rows must annihilate an \(r\)-dimensional image. Hence
\[
\operatorname{codim} Z_{\mathrm{red}}
=\min_r(\delta_r+tr).
\]

Since
\[
D(\rho)=\operatorname{codim}\{\operatorname{rank}Z_{\mathrm{deep}}\le \rho\}
       =\min_{r\le \rho}\delta_r,
\]
we get, purely by rearranging finite minima,
\[
\begin{aligned}
\min_\rho(D(\rho)+t\rho)
 &=\min_\rho\min_{r\le\rho}(\delta_r+t\rho)\\
 &=\min_r(\delta_r+tr),
\end{aligned}
\]
because \(t\ge0\), so for fixed \(r\) the cheapest choice is \(\rho=r\).

No irreducible-component decomposition occurs. In Lean, one should prove the same identity by reindexing the banked QIP formula:
\[
D(\rho)=\operatorname{cCodim}(M_2,\ldots,M_L;\rho)
       =\minAdm(M_2-\rho,\ldots,M_L-\rho).
\]
That is finite arithmetic, not formal algebraic geometry.

### Q2 — ELEMENTARY [DERIVED]

Yes. Fix \(Z\) of rank \(r\), and factor it as
\[
Z=UV,
\]
where \(U\) has full column rank \(r\) and \(V\) has full row rank \(r\). Then
\[
\operatorname{rank}(AZ)=\operatorname{rank}(AU).
\]
Moreover, \(A\mapsto AU\) is surjective onto the space of \(b\times r\) matrices: a left inverse of \(U\) supplies a preimage of every such matrix.

Therefore
\[
\operatorname{rank}(AZ)<\min(b,r)
\]
is the inverse image of the ordinary rank-deficient determinantal locus in the free \(b\times r\) matrix space. It is cut out by maximal minors, is proper, and has Lebesgue measure zero. Thus
\[
\operatorname{rank}(A_{\mathrm{cor}}Z)=\min(b,r)
\quad\text{for a.e. free }A_{\mathrm{cor}}.
\]

This is genericity in a free affine variable, not generic rank on a component of \(Z_{\mathrm{red}}\).

It gives nonvanishing a.e.; it does not by itself give a uniform lower bound for a chosen minor near rank-drop boundaries.

### Q3 — GAP, but not NEEDS-AG [DERIVED]

The component identification is genuinely unnecessary.

Indeed, suppose an exact-rank-\(r\) incidence stratum actually realizes \(\operatorname{codim}Z_{\mathrm{red}}=C_t\). Then
\[
D(r)+tr\le \delta_r+tr=C_t.
\]
The back-peel identity gives the reverse inequality, so \(r\) is a co-minimizer. Steps (2)–(4) therefore imply
\[
r\ge a+b-1\ge b.
\]
Thus every codimension-minimizing exact-rank stratum has sufficient deeper rank, without assigning a “generic rank” to any irreducible component.

The gap is the final sentence:

> lower rank has strictly higher codimension \(\Rightarrow\) recurse with more slack.

Higher codimension alone does not control singular integrability: vanishing order can increase on the lower stratum. For example,
\[
f(x,y)=x^2(x^2+y^{2N})
\]
vanishes generically quadratically along \(x=0\), giving threshold \(1/2\), but the higher-codimension point \((0,0)\) has threshold
\[
\frac{N+1}{4N}<\frac12 \qquad(N>1).
\]
Accordingly, neighborhoods of deficient-rank cells require a quantitative minor-sector cover, Jacobian accounting, and a coupled recursive estimate. Exact-rank cells being Borel or constructible is not enough.

### Q4 — GAP [INFERRED]

The component-free transversality result is a bounded native build:

- back-peel arithmetic;
- binding-cut convexity;
- the elementary free-matrix generic-rank lemma;
- finite minor refinements.

There is no Mathlib-frontier AG wall.

But the entire advertised route (including the lower-rank recursion) is not yet a one-lemma build. It still needs a quantitative rank-stratified descent theorem showing that every deficient-rank neighborhood is covered by recursive charts whose Jacobian and vanishing-order charges retain the required threshold.

**Does the route avoid the AG infrastructure? YES.** It does not smuggle in irreducible components or generic rank on components.

**Single new lemma for the component-free rank goal:**  
\[
\boxed{\minAdm(t,M_2,\ldots,M_L)
=\min_\rho\bigl(\operatorname{cCodim}(M_2,\ldots,M_L;\rho)+t\rho\bigr)}
\]
the `minAdm_eq_backPeel` lemma.

For the full analytic recursion, however, no honest single-lemma closure has yet been supplied; the missing work is the quantitative deficient-rank descent, not AG.