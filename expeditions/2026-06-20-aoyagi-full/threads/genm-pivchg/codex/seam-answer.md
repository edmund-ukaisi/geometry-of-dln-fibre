### Q1

[exact]  
\[
g(P)=G(PP^\top),\qquad   
G(Q)=\int_{[-1,1]^{m_0m_1}}\!\!\operatorname{tr}(AQA^\top)^{-c'}\,dA.
\]
Thus \(g(PV)=g(P)\) for orthogonal \(V\), even though this can redistribute the column minors. However, on a cube \(g\) is generally **not** a function only of the eigenvalues of \(PP^\top\): left rotations change the orientation of the quadratic form relative to the cube. Singular-value-only invariance would hold for a ball or Gaussian measure.

If \(\sigma_q(P)\ge\varepsilon\), then
\[
\sup g(P)<\infty\quad\Longleftrightarrow\quad c'<\frac{m_0q}{2},
\]
with the reverse implication understood whenever rank-\(q\) matrices occur in the region. Indeed,
\[
\|AP\|_F^2\ge \varepsilon^2\|A\Pi_q\|_F^2,
\]
and the transverse dimension is \(m_0q\); at \(c'\ge m_0q/2\), every rank-\(q\) point has a power/log divergence.

One-line reason: \(g\) sees the full Gram matrix but no pivot-chart label, and away from \(\sigma_q=0\) its only possible singularity is the \(m_0q\)-dimensional origin in the transverse \(A\)-variables.

### Q2

[exact] The seams do **not** concentrate on \(\{\operatorname{rank}P\le q-1\}\). They are ordinary angular algebraic hypersurfaces that meet rank-\(q\), and often higher-rank, matrices with \(\sigma_q=O(1)\); the deep stratum is merely contained in every seam because all \(q\)-minors are then zero.

For example,
\[
P=\begin{pmatrix}1&0&1\\0&1&1\end{pmatrix}
\]
has its three \(2\times2\) minors of absolute value \(1\), while \(\sigma_2(P)=1\).

One-line reason: equality of two nonzero minors is independent of rank degeneration, whereas \(\sigma_q\to0\) is precisely approach to rank \(\le q-1\) (exactly in operator distance, and comparably in Frobenius distance).

### Q3

[exact] For an SVD \(P=U\Sigma V^\top\),
\[
\det P[\rho,\kappa]
 =\sum_{\substack{I\subseteq\{1,\dots,s\}\\ |I|=q}}
   \det U[\rho,I]\det V[\kappa,I]\prod_{i\in I}\sigma_i,
\qquad s=\min(m_1,m_L).
\]
Consequently, a fixed minor may vanish faster—or identically—because its angular coefficients vanish or cancel.

In contrast, if
\[
M_q(P):=\max_{\rho,\kappa}|\det P[\rho,\kappa]|,
\]
then, writing \(R=\binom{m_1}{q}\) and \(C=\binom{m_L}{q}\),
\[
\frac{\sigma_1\cdots\sigma_q}{\sqrt{RC}}
 \le M_q(P)\le \sigma_1\cdots\sigma_q.
\]
Hence every **dominant** pivot has the correct singular-value rate; two tied dominant pivots are exactly equal. Non-dominant pivots need not.

For example,
\[
P(t)=\begin{pmatrix}1&0&0\\0&t&t^2\end{pmatrix}
\]
has minors \(t,t^2,0\), while \(\sigma_1\sigma_2\asymp t\). Using the \(t^2\)-pivot can therefore over-charge a chartwise bound.

One-line reason: the matrix of \(\bigwedge^qP\) consists of the \(q\)-minors and has operator norm \(\sigma_1\cdots\sigma_q\), so its largest coordinate is comparable to that product, but an arbitrary coordinate need not be.

### Q4

[exact] If “per-chart bulk finiteness” means
\[
\int_{C_i}h_i(P)\,dP<\infty
\]
over the complete dominant cell, including points arbitrarily close to its seams and deep boundary, then
\[
\int g(P)\,dP\le\sum_{i=1}^N\int_{C_i}h_i(P)\,dP<\infty.
\]
No surface or boundary term is created by restricting a Lebesgue integral to finitely many measurable cells.

A value \(+\infty\) only on a null seam is harmless. A factor such as
\[
\operatorname{dist}(P,\text{seam})^{-\alpha}
\]
can be harmful because it diverges throughout neighborhoods of the seam; that would already make the corresponding per-chart integral infinite. Intrinsic \(g\) contains no inverse minor-gap, so a seam with nonzero pivots creates no such singularity. At the deep intersection, any divergence is a \(\sigma_q\to0\) divergence, not a seam divergence.

[exact] Dominance is not needed for the intrinsic integral or the finite-sum principle. It is load-bearing for the **conditioning and integrability of particular shear bounds**: Cramer/shear coefficients become ratios of minors bounded by \(1\), and the pivot is comparable to \(\sigma_1\cdots\sigma_q\). A non-dominant pivot can produce an artificially divergent majorant.

One-line reason: seams are only partition boundaries; dominance prevents the coordinate proof from introducing a pivot much smaller than the intrinsic rank scale.

### Q5

[exact] Let \(\mu\) be the pushforward of factor-box Lebesgue measure under \(X\mapsto X_1\cdots X_{L-1}\). For any finite measurable partition,
\[
\int g(P)\,d\mu(P)
 =\sum_i\int_{C_i}g(P)\,d\mu(P),
\]
so the no-boundary-term conclusion holds for \(\mu\) just as for Lebesgue measure.

One must nevertheless prove per-chart finiteness with respect to the **factor measure**, not \(dP\): the pushforward can be singular and can have different concentration near \(\sigma_q=0\). For free factors with every bottleneck dimension at least \(q\), seam preimages are zero sets of nonzero polynomials and hence have factor-Lebesgue measure zero. If a bottleneck is \(<q\), the product lies in the deep rank stratum identically; any divergence is then structural rank degeneration, not a seam effect.

One-line reason: finite measurable decomposition is measure-independent, but the distribution of singular values near the deep stratum is not.

### Bottom line

**No genuine Beta/boundary divergence can hide at dominant-minor cover seams.** Under the assumed actual per-chart integrability, the finite assembly is automatically finite.

For Lean, the assembly should ensure:

- a finite measurable cover, preferably a disjoint least-index-argmax partition to assign ties;
- the chosen pivot is dominant and nonzero on the rank-\(\ge q\) cell;
- each majorant holds almost everywhere on the entire cell and is integrable up to both seams and \(\sigma_q\to0\);
- no unproved inverse-gap factor such as \((|\det B_i|-|\det B_j|)^{-1}\);
- for product tails, integrability is stated under the pulled-back factor measure.

A divergent non-dominant-pivot or inverse-gap bound is a failure of that particular bound—not evidence that the original integral diverges.