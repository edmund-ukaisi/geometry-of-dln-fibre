**Verdict**

The obstruction is real. A proof can stay “elementary” only if it includes an explicit pivot-chart normal-slice lemma for product-rank strata. If that lemma is forbidden, the front peel does not close from the listed tools alone.

The reason is that after the full-rank Gram change the factor
\[
\det(Q_bQ_b^T)^{-(M_0-t)/2}
\]
is singular on product-rank-deficient loci, and those singularities are not automatically dominated by codimension. They are exactly determinantal singularities of a matrix product.

**Candidate Routes**

(i) **Product pivot charts:** repairable, but only by proving the normal-slice content in coordinates.

If \(Q_b=A_1'\cdots A_{N-1}\) has rank \(q\), a pivot chart for \(Q_b\) gives a Schur complement \(\Omega(Q_b)\). But to integrate over the original layer variables, one must identify
\[
\Omega(Q_b)
\]
with the product of Schur complements of the individual layers, up to bounded invertible factors:
\[
\Omega(Q_b)\sim \Gamma_1\Gamma_2\cdots \Gamma_{N-1},
\]
with shifted widths
\[
(M_1-t-q,\; M_2-q,\;\dots,\;M_N-q).
\]
That is precisely the product-rank normal-slice isomorphism, just written concretely. So (i) works only in this repaired form.

(ii) **“IH covers the prefactor for free”:** false as stated.

The determinant factor vanishes when \(Q_b\) drops rank, not only when \(Q_b=0\). The shorter-chain IH controls integrals of
\[
\| \text{product} \|^{-2c}
\]
near product-zero loci. It does not control inverse Gram determinants near nonzero rank-deficient products. To make IH relevant, one must pass to the Schur complement normal product, i.e. the shifted chain. Again, this is the normal-slice step.

(iii) **Domination by higher codimension:** false.

Higher codimension is not enough; one must compare codimension with vanishing order. In the micro-example below, the rank-deficient locus has codimension \(2\) and the Gram determinant vanishes quadratically, giving threshold \(1\). The exponent appearing from the Gram change is also \(1\), so the integral is logarithmically divergent. There is no spare domination margin.

**Micro-Example**

Let
\[
W\in \mathbb R^{2\times 3},\qquad A\in\mathbb R^{3\times 4},\qquad Q=WA,
\]
and consider
\[
I_\alpha=\int \det(QQ^T)^{-\alpha}\,dW\,dA.
\]

The exact threshold is
\[
I_\alpha<\infty \quad\Longleftrightarrow\quad \alpha<1.
\]

Divergence at \(\alpha\ge 1\): take \(A\) near \([I_3\;0]\). Then
\[
\det(WAA^TW^T)\asymp \det(WW^T).
\]
Near
\[
W=\begin{pmatrix}1&0&0\\ u&x&y\end{pmatrix},
\]
we have
\[
\det(WW^T)=x^2+y^2.
\]
Thus the local integral contains
\[
\int (x^2+y^2)^{-\alpha}\,dx\,dy,
\]
which diverges exactly for \(\alpha\ge 1\).

Finiteness for \(\alpha<1\): the sharp chart is the rank-one product chart. Choose compatible \(1\times1\) pivots in \(W\) and \(A\). The Schur complements have sizes
\[
W^\sharp\in\mathbb R^{1\times2},\qquad A^\sharp\in\mathbb R^{2\times3},
\]
and the Schur complement of \(WA\) is, up to bounded invertible factors,
\[
W^\sharp A^\sharp.
\]
On that chart,
\[
\det(WA(WA)^T)\asymp \|W^\sharp A^\sharp\|^2.
\]
The threshold for
\[
\int \|wB\|^{-2\alpha}\,dw\,dB,\qquad w\in\mathbb R^{1\times2},\ B\in\mathbb R^{2\times3},
\]
is
\[
\alpha<\frac12\minAdm(1,2,3)=\frac12\cdot 2=1.
\]
Other rank charts give thresholds \(\ge 1\), so the global threshold is exactly \(1\).

For your concrete exponent,
\[
(M_0-t)/2=(3-1)/2=1,
\]
so
\[
\int \det(WA_2(WA_2)^T)^{-1}\,dW\,dA_2
\]
is exactly critical and diverges logarithmically.

Thus the determinant prefactor is **at** the threshold, not strictly inside it. Since convergence is strict, it is outside the usable finiteness range. The budget
\[
c'<\frac12\minAdm(3,3,3,4)=7/2
\]
does not by itself make this prefactor integrable.

What I can prove: the micro-example threshold is exactly \(1\), and the naive full-rank Gram prefactor cannot be integrated independently.

What I would not claim as a theorem: that no possible proof exists outside this framework. But for the specific tools listed, the missing ingredient is exactly a product-rank normal-slice analysis, whether stated abstractly or encoded by explicit Schur pivot charts.