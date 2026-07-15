## Verdict: FALSE

Everything below is proved exactly; no Monte Carlo or inference is used.

### 1. The regions are disjoint

Let \(N_\varepsilon(Q)\) be the number of singular values below \(\varepsilon\). Since \(j<r\),

\[
D_{\mathrm{LHS}}
=\{(z,A_{\rm cor}):N_\varepsilon(\operatorname{hsQ}(z,A_{\rm cor}))=j\}.
\]

In contrast,

\[
D_{\mathrm{RHS}}
=\{(z,A_{\rm cor}):\operatorname{hsQ}\operatorname{hsQ}^{T}
 \succeq \varepsilon ^2I\}
=\{N_\varepsilon(\operatorname{hsQ})=0\}.
\]

Because \(j\ge1\), these predicates are disjoint, not equal or nested when both regions are nonempty.

### 2. Minimal nonvacuous square counterexample

Take

\[
M_0=M_1=M_2=n=3,\qquad t=j=1,\qquad r=2,\qquad u=2,
\]
\[
\varepsilon=\frac18,\qquad c'=4,
\]

and let \(\kappa\) select the first two rows. Use one free deep layer \(Z\in[-1,1]^{3\times3}\), so

\[
W=A_0Z.
\]

These dimensions are minimal with \(j<r\) and a nonempty full-row-rank pivot shell.

Consider

\[
Z_*=\frac12 I_3,\qquad
A_{0,*}=\operatorname{diag}\left(\frac12,\frac12,0\right),
\qquad
W_*=\operatorname{diag}\left(\frac14,\frac14,0\right).
\]

Thus \(W_*\) has exactly one singular value below \(1/8\).

#### Exponent arithmetic

At corank \(1\), the divergence threshold is

\[
\frac{M_0(M_1-1)}2=\frac{3\cdot2}{2}=3.
\]

Hence \(c'=4\) is above the corank-one threshold. But

\[
4<\frac{M_0M_1}{2}=\frac92,
\]

so \(G(Q)\) remains finite at every full-rank \(Q\).

If \(W\) is near \(W_*\), with smallest singular value \(s>0\), the other two singular values stay bounded above and below. In singular-value coordinates, write \(T=(X\mid y)\), where \(X\) has \(6\) real coordinates and \(y\) has \(3\). Then

\[
G(W)\asymp
\int \bigl(\|X\|^2+s^2\|y\|^2\bigr)^{-4}\,dX\,dy
\asymp s^{6-8}=s^{-2}.
\]

Indeed, integration in \(X\in\mathbb R^6\) gives \(Cs^{-2}\|y\|^{-2}\), and \(\|y\|^{-2}\) is locally integrable in \(\mathbb R^3\).

#### The outer \(A'\)-integral diverges

Parameterize matrices near \(W_*\) by

\[
W=
\begin{pmatrix}
B&b\\
c^T&c^TB^{-1}b+\delta
\end{pmatrix},
\]

where \(B\) is near \(\frac14I_2\). Then

\[
\det W=(\det B)\delta,
\]

so the smallest singular value satisfies \(s\asymp|\delta|\). A sufficiently small neighborhood lies entirely in shell \(j=1\), by Weyl’s inequality:

\[
\sigma_2(W)>\frac18,\qquad \sigma_3(W)<\frac18.
\]

Therefore

\[
G(W)\asymp |\delta|^{-2},
\qquad
\int_{-\eta}^{\eta}|\delta|^{-2}\,d\delta=+\infty.
\]

Finally, near \(Z_*\), \(Z\) is invertible and the change of variables \(W=A_0Z\) has

\[
dA_0=|\det Z|^{-3}\,dW,
\]

with this Jacobian bounded above and below. Hence the divergence survives integration over the original boxed parameters:

\[
\boxed{\mathrm{LHS}=+\infty}.
\]

#### The RHS is finite

On the pivot shell,

\[
QQ^T\succeq\varepsilon^2I_3,
\]

and therefore

\[
\|TQ\|_F^2\ge\varepsilon^2\|T\|_F^2.
\]

Thus

\[
G(Q)\le
\varepsilon^{-8}
\int_{[-1,1]^9}\|T\|_F^{-8}\,dT<\infty,
\]

because \(8<9\). This bound is uniform in \(Q\), and all outer parameter boxes have finite measure. Consequently,

\[
\boxed{\mathrm{RHS}<+\infty}.
\]

### 3. Strictness does not rescue the claim

This witness has

\[
j=1<2=r.
\]

Thus excluding the saturated shell \(j=r\) does not help. For \(j=r\), the LHS condition becomes \(N_\varepsilon(Q)\ge r\), which is likewise disjoint from the RHS condition \(N_\varepsilon(Q)=0\).

\[
\boxed{\text{The proposed inequality is FALSE even for }1\le j<r.}
\]