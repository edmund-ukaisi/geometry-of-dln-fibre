**Notation**

Let
\[
\Phi(a,b,q)=\min_{0\le r\le \min(b,q)}\{a r+(b-r)(q-r)\}.
\]
All thresholds below are for bounded boxes near the origin.

**Q1. Base Case**

Because \(C'\) is bounded,
\[
\|B_0\|^2+\|C'B_0+\Gamma Q_b\|^2
\asymp
\|B_0\|^2+\|\Gamma Q_b\|^2.
\]
So \(C'\) does not affect the RLCT.

For \(h=\|\Gamma Q_b\|^2\), a determinantal rank-stratum resolution, equivalently the singular-value Laplace estimate, gives
\[
\lambda(h)=\frac12\Phi(a,b,q).
\]
Indeed, near the stratum where \(Q_b\) has active rank \(r\), the cost of forcing \(Q_b\) to rank \(\le r\) is \((b-r)(q-r)\), and the \(r\) active directions impose \(a r\) quadratic directions in \(\Gamma\). Thus the candidate exponent is
\[
\frac12\{a r+(b-r)(q-r)\},
\]
and minimizing over \(r\) gives the exact threshold.

Then by the direct-sum rule,
\[
\boxed{\lambda(f)=\frac{tq}{2}+\frac12\Phi(a,b,q).}
\]

Mellin/radial form:
\[
f^{-c}=\frac1{\Gamma(c)}\int_0^\infty s^{c-1}e^{-s f}\,ds,
\]
and
\[
\int e^{-s\|B_0\|^2}\,dB_0\sim s^{-tq/2},\qquad
\int e^{-s\|\Gamma Q_b\|^2}\,d\Gamma\,dQ_b\sim s^{-\Phi/2}.
\]
Hence the large-\(s\) Mellin integral converges exactly when
\[
c<\frac{tq+\Phi(a,b,q)}2.
\]

Zero locus:
\[
\{f=0\}=\{B_0=0,\ \Gamma Q_b=0\},
\]
with \(C'\) free. The codimension of \(\{\Gamma Q_b=0\}\) is exactly \(\Phi(a,b,q)\), so here
\[
\lambda(f)=\frac12\operatorname{codim}\{f=0\}.
\]
This equality is proven by the resolution above; it is not a general codimension principle.

Example: \(a=2,b=1,q=2,t=1\). Then \(\Phi=\min(2,2)=2\), so
\[
\lambda(f)=\frac{2}{2}+\frac{2}{2}=2.
\]
The zero locus has codimension \(2+2=4\).

**Q2. Bilinear Leaf**

For
\[
g=\|B_0\|^2+\|C'B_0+\gamma z\|^2,
\qquad \gamma\in\mathbb R^a,\ z\in\mathbb R^D,
\]
boundedness of \(C'\) again gives
\[
g\asymp \|B_0\|^2+\|\gamma z\|^2.
\]
Since
\[
\|\gamma z\|^2=\|\gamma\|^2\|z\|^2,
\]
the product rule gives
\[
\lambda(\|\gamma z\|^2)=\min\left(\frac a2,\frac D2\right).
\]
Therefore
\[
\boxed{\lambda(g)=\frac{tq}{2}+\frac12\min(a,D).}
\]
If \(D=q\), this is exactly \(\frac12(tq+\min(a,q))\).

So yes: the coupling term \(C'B_0\) does not change the threshold. It is absorbed by two-sided comparability on a bounded \(C'\)-box.

Example: \(a=3,D=2,t=1,q=2\). Then
\[
\lambda(g)=1+\frac12\min(3,2)=2.
\]

**Q3. Whole-Plane \(\Gamma\) Integration**

The determinant weight is
\[
\det(Q_bQ_b^T)^{-a/2}.
\]
If \(a>0\) and \(q<b\), then \(Q_bQ_b^T\) is always singular, so the weight is not locally integrable.

Assume \(q\ge b\). Near the smooth corank-one locus \(\operatorname{rank}Q_b=b-1\), there are normal coordinates \(z\in\mathbb R^{q-b+1}\) such that
\[
\det(Q_bQ_b^T)\asymp \|z\|^2.
\]
Thus the local integral contains
\[
\int_0^\varepsilon r^{q-b}\,r^{-a}\,dr,
\]
which converges iff
\[
q-b+1>a.
\]
Deeper rank drops give conditions \(q-b+k>a\), \(k\ge1\), so the strictest is \(k=1\).

Hence, for \(a>0\),
\[
\boxed{\int \det(Q_bQ_b^T)^{-a/2}\,dQ_b<\infty
\iff q\ge a+b.}
\]
It diverges for \(q\le a+b-1\), with logarithmic divergence on the boundary \(q=a+b-1\).

Example: \(a=2,b=1,q=2\). The weight is \(\|z\|^{-2}\) on \(\mathbb R^2\), so
\[
\int_{|z|<\varepsilon}\|z\|^{-2}\,dz
\]
diverges logarithmically.

**Q4. Bounded Box vs Regime A**

For \(a=2,b=1,q=2,t=1\), the true bounded-box threshold from Q1 is
\[
\lambda=2.
\]
Regime A emits the divergent weight \(\|z\|^{-2}\), but the original bounded integral is still finite for every \(c'<2\).

The reason is saturation. In the bounded problem,
\[
f\asymp \|B_0\|^2+\|\gamma\|^2\|z\|^2,
\]
so the integral is controlled by
\[
\int r_B^{1}r_\gamma^{1}r_z^{1}
(r_B^2+r_\gamma^2r_z^2)^{-c'}\,dr_B\,dr_\gamma\,dr_z,
\]
whose threshold is
\[
\frac{2}{2}+\min\left(\frac22,\frac22\right)=2.
\]
The determinant singularity is not a genuine obstruction below the true RLCT; it is created by integrating \(\Gamma\) over all of \(\mathbb R^{ab}\).

For general \(b\), the corank-one bounded leaf has
\[
D=q-b+1,\qquad
\lambda_{\text{leaf}}=\frac{a(b-1)}2+\frac12\min(a,D).
\]
When Regime A diverges, \(D\le a\), this becomes
\[
\frac{a(b-1)+D}{2}.
\]
So the singularity resurfaces as a smaller finite RLCT contribution, not as a non-integrable determinant weight. A single leaf proves only its chart; the global base threshold is still the minimum over all ranks from Q1.

**Q5. Product \(Q_b=YA\)**

If \(A\) is fixed of rank \(\rho\), then \(z=yA\) is only \(\rho\)-dimensional. The leaf threshold is
\[
\boxed{\frac12\min(a,\rho).}
\]
So a fixed full-rank \(A\) with \(\rho\ge \min(a,D)\) behaves like the free \(z\)-model; otherwise it lowers the threshold.

If \(A\) is free, the leaf is
\[
\|\gamma\,yA\|^2=\|\gamma\|^2\|yA\|^2.
\]
Since \(yA\) is a two-layer chain \((1,m,D)\),
\[
\lambda(\|yA\|^2)=\frac12\min(m,D),
\]
and the product rule gives
\[
\boxed{\lambda_{\text{twisted leaf}}=\frac12\min(a,m,D).}
\]
Compared with the base free-\(z\) leaf \(\frac12\min(a,D)\), the product structure lowers the threshold exactly when
\[
\boxed{m<\min(a,D).}
\]

For the corank-one peel of a \(b\times q\) matrix, \(D=q-b+1\). Thus the exact lowering regime is
\[
\boxed{m<\min(a,q-b+1).}
\]

Example: \(a=2,b=1,q=2,m=1,t=1\). Free \(Q_b\) gives
\[
\lambda=1+\frac12\min(2,2)=2.
\]
But \(Q_b=yA\) with \(y\in\mathbb R\), \(A\in\mathbb R^{1\times2}\) gives
\[
\lambda=1+\frac12\min(2,1,2)=\frac32.
\]
So the bilinear free-row reduction overestimates the threshold in the twisted product case.