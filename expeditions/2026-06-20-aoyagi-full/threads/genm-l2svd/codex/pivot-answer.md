## Q1 — Top stratum: yes, with qualifications

For fixed \(Q_b\) of full row rank, the reduction is correct and proves finiteness provided

\[
t\le b,\qquad a<b-t+1,
\]

and the \(P\)-domain is compactly contained in \(GL_t\).

Indeed,

\[
B_{12}=PB',\qquad dB_{12}=|\det P|^b\,dB',
\]

because each of the \(b\) columns is multiplied by \(P\).

Choose \(V\in O(q)\) with

\[
Q_bV=[\Psi\mid 0],\qquad |\det\Psi|=\prod_{j=1}^b\sigma_j(Q_b).
\]

Writing \(Q_pV=[R_1\mid R_2]\),

\[
\widetilde QV=[R_1+B'\Psi\mid R_2].
\]

For \(W=R_1+B'\Psi\), each of the \(t\) rows is right-multiplied by \(\Psi\), so

\[
dW=|\det\Psi|^t\,dB',
\qquad
dB'=|\det\Psi|^{-t}\,dW.
\]

Moreover,

\[
\widetilde Q\widetilde Q^T=WW^T+C_0,\qquad C_0=R_2R_2^T\succeq0.
\]

The PSD determinant inequality is valid. For \(A\succ0\),

\[
\det(A+C_0)
=\det A\,
\det\!\left(I+A^{-1/2}C_0A^{-1/2}\right)
\ge \det A,
\]

since every eigenvalue of the second factor is at least \(1\). For singular \(A\), apply this to \(A+\varepsilon I\) and let \(\varepsilon\downarrow0\). Hence

\[
\det(WW^T+C_0)^{-a/2}
\le \det(WW^T)^{-a/2}.
\]

Thus, for a suitable ball,

\[
I(Q_b)
\le C\,|\det\Psi|^{-t}
\int_{\|W\|\le R}\det(WW^T)^{-a/2}\,dW<\infty
\]

by QBOX.

The qualifications are:

- If the bounded set of invertible \(P\)'s approaches \(\det P=0\), then \(P^{-1}B_{12}\) is not uniformly bounded, so the fixed-ball argument is incomplete.
- This is pointwise, or locally uniform on compact subsets of the full-rank \(Q_b\)-stratum. It is not uniform as \(\sigma_{\min}(Q_b)\to0\).
- The orthogonal \(V\) causes no coupling for the Gram factor: it is only an algebraic identity. Other non-orthogonally-invariant or singular integrand factors must still be tracked separately.
- No globally smooth SVD choice is needed for the pointwise estimate; if differentiation in \(A'\) is required, one should use local rank charts instead.

So: **yes for the isolated top-stratum disposal; no as a complete estimate through the rank boundary.**

## Q2 — Free \(Q_b\): exact threshold

Let

\[
F(Q_b)=|\det\Psi|
=\sqrt{\det(Q_bQ_b^T)}
=\prod_{i=1}^b\sigma_i(Q_b).
\]

For a free real \(b\times q\) matrix, \(b\le q\),

\[
\boxed{\int_{\text{bounded}}F(Q_b)^{-\tau}\,dQ_b<\infty
\iff \tau<q-b+1.}
\]

Setting \(\tau=t\), the required condition is

\[
\boxed{t<q-b+1.}
\]

For integral \(t\), this is \(q\ge b+t\). Equality gives logarithmic divergence.

An elementary proof uses the thin QR decomposition of \(Q_b^T\in\mathbb R^{q\times b}\):

\[
Q_b^T=UR,\qquad
dQ_b=C\prod_{i=1}^b r_{ii}^{\,q-i}\,dR\,dU,
\qquad F(Q_b)=\prod_{i=1}^b r_{ii}.
\]

The diagonal integrals behave like

\[
\int_0^\varepsilon r_{ii}^{\,q-i-\tau}\,dr_{ii},
\]

so one needs \(\tau<q-i+1\) for every \(i\). The strongest condition occurs at \(i=b\).

The rank-\(r\) stratum has dimension

\[
br+rq-r^2=r(b+q-r),
\]

and therefore codimension

\[
c_r=bq-r(b+q-r)=(b-r)(q-r).
\]

Writing \(s=b-r\), the transverse product of the \(s\) vanishing singular values has radial order \(s\). A radial blow-up therefore gives

\[
\tau s<c_r
\iff
\tau<\frac{(b-r)(q-r)}{b-r}=q-r.
\]

Taking all strata,

\[
\min_{0\le r<b}(q-r)=q-b+1.
\]

Thus this is a standard submersive determinantal computation. Codimension alone is not enough; it must be divided by the vanishing order \(b-r\).

## Q3 — Product-parametrized \(Q_b\): no unchanged carry-over

**Fact:** Non-submersive pullback can change both codimension and integrability threshold.

For example, take free factors

\[
Q_b=LR,\qquad
L\in\mathbb R^{b\times b},\quad
R\in\mathbb R^{b\times q}.
\]

Then

\[
F(LR)
=\sqrt{\det(LRR^TL^T)}
=|\det L|\,F(R).
\]

Consequently the pullback integral requires simultaneously

\[
t<1
\quad\text{and}\quad
t<q-b+1,
\]

so its threshold is

\[
\boxed{t<1.}
\]

When \(q>b\), this is strictly worse than the free-output threshold \(t<q-b+1\). Geometrically, the output corank-one locus has codimension \(q-b+1\), but its preimage contains the divisor \(\det L=0\), of codimension \(1\), along which \(F(LR)\) vanishes linearly.

The cokernel dimension of the multiplication differential confirms that the submersion argument fails, but it does not by itself determine the pullback discrepancy: one also needs the codimensions of every factor-rank incidence component and the precise vanishing order along each component.

**Inference for the proposed proof:** the deeper-product transverse Jacobian is a genuine unresolved proof obligation. It does not follow from Q2 or from the cokernel count. Rank-normal forms, incidence stratifications, and iterative QR/SVD are standard tools, but deriving the exact exponent for a specified multi-factor product is a research-grade calculation—not an automatic standard determinantal substitution. Whether it is literally an open problem depends on the precise product dimensions and rank patterns.