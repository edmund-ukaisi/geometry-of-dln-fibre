### Q1 — VERDICT: survives

**Fact.** Writing \(A_2=\binom{X}{r}\),

\[
w=\|P(Q_p+P^{-1}B_{12}Q_b)\|_F^2
 =\|[P\mid B_{12}]A_2A_3\|_F^2
 =\|\Gamma'A_3\|_F^2,
\]

with

\[
\Gamma'=[P\mid B_{12}]A_2=PX+B_{12}r.
\]

This is polynomial, \(P^{-1}\)-free, and has exactly the tied-tail γ′ form for \((2,2,2)\). The rows \(C\) occur only in the nonnegative rational residual.

Thus, for \(e=c'-\tfrac12>0\),

\[
\mathrm{Base}^{-e}\le w^{-e}.
\]

The comparator—not `Base` itself—has

\[
D'.\mathrm{decLoss}
  =|u_0|^{2k}\|\Gamma'A_3\|_F^2.
\]

Its carrier can be indexed by \(\operatorname{Fin}2\times\operatorname{Fin}2\), with residuals precisely the entries of \(\Gamma'A_3\).

**Inference.** Provided “free front block” means an independent coordinate block disjoint from the tied \(A_2,A_3\) coordinates, replacing literal \(A_1\) by \(\Gamma_D\) creates no new algebraic obstruction. The block partition and the shear

\[
D_D\longmapsto \Gamma=D_D-CP^{-1}B_{12}
\]

are the same, with shear Jacobian \(1\). The reduced object handed to the IH is the externally dominating \(w\)-decoration, not the rational `Base`-decoration.

### Q2 — VERDICT: survives chartwise

For fixed \(P,B_{12},r\), the absorption map is

\[
X\longmapsto\Gamma'=PX+B_{12}r,
\qquad
X=P^{-1}(\Gamma'-B_{12}r).
\]

It is an affine bijection whenever \(P\) is invertible. Since \(X\) has two columns,

\[
dX=|\det P|^{-2}\,d\Gamma'.
\]

On a pivot chart uniformly separated from \(\det P=0\), this is a bounded spectator-dependent unit. After the residual is dropped, the integrand is independent of \(C\); its bounded-domain integral contributes only a constant.

Likewise, on a Gram-units sector

\[
Q_bQ_b^\top\ge\delta>0,
\]

the factor \((Q_bQ_b^\top)^{-1/2}\le\delta^{-1/2}\) is bounded. Neither it nor \(|\det P|^{-2}\) must be inserted into the reduced Jacobian. One bounds them externally and, if necessary, enlarges the transformed parameter domain to a fixed box. This produces an admissible comparator integral, though not an exact measure-preserving identification with the banked output.

Mere conditions \(P\) invertible and \(Q_b\ne0\), without uniform lower bounds, are insufficient.

### Shared radial and accumulated Jacobian

**VERDICT: monomial and threshold-exact.**

After the freed-block integration, the radial exponent remains

\[
|u_0|^{\mathrm{jac}_0-2kc'}.
\]

Set \(e=c'-\tfrac12\) and

\[
\mathrm{jac}'_0=\mathrm{jac}_0-k.
\]

Then the reduced comparator contributes exactly

\[
|u_0|^{\mathrm{jac}'_0}
  \bigl(|u_0|^{2k}w\bigr)^{-e}
=
|u_0|^{\mathrm{jac}_0-2kc'}w^{-e}.
\]

More generally, with peel charge \(m=ab\), one takes
\(\mathrm{jac}'_0=\mathrm{jac}_0-km\). Consequently,

\[
\frac{\mathrm{jac}'_0+1}{2k}
=
\frac{\mathrm{jac}_0+1}{2k}-\frac m2,
\]

which is exactly the reduced threshold when
\(\minAdm(\mathrm{redChain})=\minAdm(M)-m\). The Gram and absorption factors remain bounded chart units, not exceptional monomials.

### Most likely hidden failure

The general-parent verdict fails if the formal “free block” clause is only syntactic—meaning \(\Gamma_D\) appears freely in the loss—but does not guarantee independent product coordinates, a suitable Lebesgue measure, and bounded fibres disjoint from the tied tail. Literal \(A_1\) has that independence automatically; an inherited \(\Gamma_D\) might not. If the landed clause guarantees genuine coordinate-level freeness, there is no new obstruction.