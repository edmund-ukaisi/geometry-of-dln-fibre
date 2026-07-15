SUMMARY VERDICT: **FINITE to 4.5** for both objects when \(c'<4.5\); both diverge logarithmically at \(c'=4.5\). [FACT]

## Section A — Pointwise threshold

[FACT] For fixed \(Q=\mathrm{hsQ}\) of rank \(R\), \(T\mapsto TQ\) has \(3R\) active directions. Hence near its kernel,

\[
\int \|TQ\|^{-2c'}\,dT
\sim \int_0^\delta r^{3R-1-2c'}\,dr,
\]

so the exact pointwise condition is

\[
c'<\frac{3R}{2}.
\]

[FACT] On the exact shell-\(2\) limiting stratum, \(\operatorname{rank}Q=1\). Thus

\[
\boxed{c'_{\mathrm{pt}}=\frac32},
\qquad
\int_0^\delta r^{2-2c'}\,dr.
\]

At \(c'=3/2\) the divergence is logarithmic.

[FACT] This rank-one stratum has outer codimension

\[
(3-1)(7-1)=12.
\]

Equivalently, \(Q_p\) having rank one has codimension \(6\), and requiring the \(Q_b\) row to lie in the same row line supplies another \(6\).

[FACT] In decorated coordinates, \(\operatorname{rank}Q=1+\operatorname{rank}W\). For \(r=\operatorname{rank}W\), the active front dimension is \(2+3r\), giving

\[
q<\frac{2+3r}{2},
\qquad
c'=q+\frac12<\frac32(1+r).
\]

Thus \(W=0\) again has the exact pointwise threshold

\[
\boxed{c'_{\mathrm{pt}}=\frac32}.
\]

Nearby full-rank outer points have threshold \(9/2\); the pointwise threshold jumps only on the rank-deficient strata.

## Section B — Integrated thresholds

### Object U

[FACT] Write the singular values of \(Q\) near a generic rank-one point as

\[
s_1\asymp1,\qquad 0<t=s_3\le s=s_2\ll1.
\]

The \(3\times7\) real singular-value measure is, up to a smooth nonzero angular factor,

\[
s^4t^4(s^2-t^2)\,ds\,dt.
\]

With \(s=\rho\), \(t=\rho\tau\), this becomes

\[
\rho^{11}\tau^4(1-\tau^2)\,d\rho\,d\tau.
\]

The power \(\rho^{11}\) is precisely the radial measure for codimension \(12\).

[FACT] After rotating \(T\),

\[
\|TQ\|^2\asymp |x|^2+s^2|y|^2+t^2|z|^2,
\qquad x,y,z\in\mathbb R^3.
\]

For \(3<c'<9/2\), exact radial integration gives

\[
F(s,t):=\int_T\|TQ\|^{-2c'}dT
\asymp s^{-3}t^{\,6-2c'}.
\]

At \(c'=3\), the corresponding power is replaced by an integrable logarithm.

[FACT] Multiplying by the singular-value measure gives

\[
F\,dQ
\asymp
\rho^{14-2c'}\tau^{10-2c'}(1-\tau^2)
\,d\rho\,d\tau.
\]

The two outer convergence conditions are

\[
14-2c'>-1\iff c'<\frac{15}{2},
\qquad
10-2c'>-1\iff c'<\frac{11}{2}.
\]

Thus the outer measure easily absorbs the rank-one and rank-two pointwise blow-ups throughout \(c'<9/2\).

[FACT] The actual binding stratum is instead \(T=0\) over any positive-measure full-rank part of the shell:

\[
\int_0^\delta r^{8-2c'}\,dr<\infty
\iff c'<\frac92.
\]

Therefore

\[
\boxed{\operatorname{threshold}(I_j)=\frac92}.
\]

### Object D

[INFERENCE] “After a change of variables” is interpreted with the induced Lebesgue Jacobian, as required for \(G\) to represent the original decorated integral.

[FACT] For \(W\) with singular values \(s\ge t\), integration over \(\widetilde H\in\mathbb R^2\) gives the same power \(A^{3/2-c'}\), because \(q=c'-1/2\). Consequently,

\[
\int_{\widetilde H,Y}
(\|\widetilde H\|^2+\|YW\|^2)^{-q}
\asymp s^{-3}t^{6-2c'}.
\]

The \(2\times6\) singular-value measure is again

\[
s^4t^4(s^2-t^2)\,ds\,dt,
\]

so the same \(\rho^{14-2c'}\tau^{10-2c'}\) absorption applies.

[FACT] For fixed rank-two \(W\), the active front dimension is \(2+6=8\). Hence the binding radial integral is

\[
\int_0^\delta r^{7-2q}\,dr
=
\int_0^\delta r^{8-2c'}\,dr,
\]

which converges exactly for \(c'<9/2\). Therefore

\[
\boxed{\operatorname{threshold}(G)=\frac92}.
\]

[FACT] The determinant decoration does not lower this threshold. In invariant \(Q_b\in\mathbb R^7\) coordinates,

\[
\det(Q_bQ_b^\top)^{-1/2}=\|Q_b\|^{-1},
\qquad
dQ_b\sim r_b^6\,dr_b,
\]

so its radial contribution is \(r_b^5dr_b\), which is integrable.

[FACT] In the pivot coordinates \(Q_b=D(1,X)\), the missing change-of-variables factor is \(|D|^6\); combined with the determinant factor it gives \(|D|^5\). If \(G\) were instead defined literally with flat \(dD\,dX\) and this Jacobian omitted, it would diverge like \(\int dD/|D|\) for every \(c'\). That would be a different object.

## Section C — Verdict on Q2/Q3/Q4

[FACT] Neither object diverges anywhere in \([3,4.5)\). Both first diverge at \(c'=4.5\), from the ordinary front-zero stratum, not from the forced rank-one outer locus.

[FACT] The shell does not remove the absorbing mechanism. It restricts \(0<t\le s<\varepsilon\), but it does not freeze \(s,t\) or discard their Jacobian

\[
s^4t^4(s^2-t^2)\,ds\,dt.
\]

That Jacobian supplies the codimension-\(12\) volume responsible for integrability.

[FACT] Subset monotonicity is valid for \(U\):

\[
0\le I_{\mathrm{shell}}(c')\le I_{\mathrm{full\ box}}(c').
\]

Since the full-box object is finite for \(c'<9/2\), the shell object must be finite there. The analogous argument is valid for \(D\) relative to its own off-shell integral once the proper transformed measure is included; a direct comparison \(G\le I_j\) is not valid because their displayed integrands differ.

[FACT] The thresholds \(3/2\) at rank one and \(3\) at rank two are pointwise-only artifacts. Those strata have ambient measure zero, and their nearby blow-ups are integrable with the singular-value Jacobian above.

[FACT] The fact that \(\|Q_p\|_F=O(1)\) is irrelevant: rank loss concerns \(W\) or the smallest singular values, while the outer transverse volume—not decay of \(\|Q_p\|_F\)—absorbs the pointwise divergence.