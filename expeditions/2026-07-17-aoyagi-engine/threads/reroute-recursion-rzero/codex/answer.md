The supplied claims are algebraically inconsistent. In the certified \((3,3,4)\) corner, the joined divisor has \(k=2\), not \(k=1\), and its ratio is \(2<4\). Thus, under the stated product factorization, there is an obstruction.

### Q1 — NO

The branch codimensions may add in the log discrepancy, but the loss orders also add.

Write

\[
\nu_D=h_D+1,\qquad N_D=\operatorname{ord}_D(F)=2k_D.
\]

For two transverse divisors \(D_q,D_u\), blowing up their intersection produces \(E\) with

\[
\nu_E=\nu_q+\nu_u,\qquad N_E=N_q+N_u.
\]

Hence

\[
\frac{h_E+1}{2k_E}
=
\frac{\nu_q+\nu_u}{N_q+N_u},
\]

a weighted average of the two old ratios—not the sum of their numerators over a fixed denominator \(2\).

If the peel and residual divisors both have \(k=1\), with

\[
\nu_q=a=(M_1-t_1)(M_2-t_1),\qquad
\nu_u=b=Mval_{\rm sub},
\]

then the joined divisor has

\[
h_E=a+b-1,\qquad k_E=2,
\qquad
\lambda_E=\frac{a+b}{4}
=\frac{Mval(t)}4,
\]

not \(Mval(t)/2\).

The additive \(Mval\) identity controls discrepancy, not multiplicity. It yields \(Mval/2\) only if one separately proves \(k_E=1\), which is incompatible with a product \(q^2u^2\).

### Q2 — YES

The \(k=1\) property fails whenever a center lies inside multiple components of the total transform.

The elementary example is

\[
F=x^2y^2.
\]

Blowing up \(x=y=0\), in the chart \(x=e,\ y=ev\),

\[
F=e^4v^2.
\]

Therefore

\[
k_E=2,\qquad h_E=1,\qquad
\frac{h_E+1}{2k_E}=\frac2{4}=\frac12.
\]

More generally, a transverse join satisfies \(k_E=\sum_i k_i\). Joined ratios cannot fall below the minimum of the constituent ratios because they are weighted averages, but they can be strictly below an incorrectly claimed additive branch value.

Clean survivor squares can prevent this only when they remain of order \(2\) along the same valuation. For a sum such as

\[
\xi_1^2+\xi_2^2+d_2^2+(d_1\mu)^2,
\]

the clean squares explain the exact RLCT \(2\); they do not establish a universal \(k=1\) rule.

### Q3 — YES, under the stated chart assumptions

Take the supplied certified case

\[
M=(3,3,4),\qquad t=(1,0).
\]

The admissible values are

\[
9,\ 8,\ 9,\ 12,
\]

so

\[
\minAdm(M)=8,\qquad \lambda_{\rm claimed}=4.
\]

Here both peel and residual codimensions equal \(4\). After their radial resolutions, the asserted product structure gives

\[
F\circ g=(qu)^2U,\qquad
|\det Dg|=q^3u^3J,
\]

with \(U,J\) units.

Now extract the divisor over the corner \(q=u=0\). Put

\[
q=e,\qquad u=ev.
\]

Then exactly

\[
F\circ g=e^4v^2U,\qquad
|\det Dg|=e^{3+3+1}v^3J=e^7v^3J.
\]

Thus

\[
k_E=2,\qquad h_E=7,\qquad
\lambda_E=\frac{7+1}{2\cdot2}=2<4.
\]

So the statement in Fact 3 that this same divisor has \(h=7\) and \(k=1\) is impossible: \(q^2u^2\) pulls back to \(e^4v^2\).

### Q4 — YES for pure \(G\)-divisors; globally the relationship is a minimum

Let

\[
m(x)=\prod_i x_i^{a_i},
\]

with \(x\) disjoint from the variables of \(G(y)\). Product integration gives

\[
\operatorname{rlct}(m^2G)
=
\min\!\left\{
\operatorname{rlct}(m^2),
\operatorname{rlct}(G)
\right\}.
\]

For Lebesgue measure,

\[
\operatorname{rlct}(m^2)
=\min_i\frac1{2a_i}.
\]

Thus, for squarefree \(m\),

\[
\operatorname{rlct}(m^2G)=\min\left\{\frac12,\operatorname{rlct}(G)\right\}.
\]

A divisor coming purely from the \(G\)-resolution retains its original ratio. A divisor joining \(m\)- and \(G\)-components has the weighted-average ratio above, so it cannot undercut both constituent ratios—but the monomial prefactor can absolutely lower the overall RLCT below \(\operatorname{rlct}(G)\).

### Proven versus inference

Proven from exact pullback algebra:

- Corner multiplicities add.
- The certified \(h=7\) corner has \(k=2\).
- Its ratio is \(2\), strictly below \(4\).

Inference about the actual Aoyagi resolution:

- If \(\minAdm/2=4\) is nevertheless the correct RLCT of the original network, then the asserted local product \(q^2u^2U\), the claimed mapping of this corner over the origin, or the claimed Jacobian bookkeeping is not the true total-transform geometry.
- A controlled transform that divides out an exceptional factor cannot be used when computing the RLCT of the original loss.

**OBSTRUCTION (a kill): under the stated product-recursion assumptions, resolving/extracting the residual corner produces a divisor of ratio \(2<\minAdm/2=4\).**