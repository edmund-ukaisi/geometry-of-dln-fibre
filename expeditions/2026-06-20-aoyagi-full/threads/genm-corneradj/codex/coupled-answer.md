## Q-A(i)

**[Exact]** Yes. The domain has volume \(2^{10}\) and the integrand is at most \(w^{-c'}\), so \(H(w)\le 2^{10}w^{-c'}<\infty\).

## Q-A(ii)

Put \(B=A_{\rm cor}Z_f\). Since \(Z_f\in GL_3\), this is an invertible linear change of the six \(A_{\rm cor}\)-coordinates.

**[Exact, assuming generic \(C_{\rm cross}\), hence \(\operatorname{rank}C_{\rm cross}=2\)]** On

\[
N=\{(\Gamma,B):C_{\rm cross}+\Gamma B=0\},
\]

both \(\Gamma\) and \(B\) have rank \(2\). Hence \(\Gamma\in GL_2\), and

\[
D\Phi(\dot\Gamma,\dot A)
 =\dot\Gamma B+\Gamma\dot A Z_f
\]

is onto \(\mathbb R^{2\times3}\): given \(Y\), take \(\dot\Gamma=0\) and
\(\dot A=\Gamma^{-1}YZ_f^{-1}\). Thus

\[
\boxed{\kappa=6},\qquad \dim N=10-6=4.
\]

Indeed \(N\) is locally the graph \(B=-\Gamma^{-1}C_{\rm cross}\).

The fixed-\(B\) split is:

\[
\underbrace{\frac{ab}{2}}_{=2}
+
\underbrace{\frac{\nu}{2}}_{=1}
=\frac{\kappa}{2}=3.
\]

Here \(\dot\Gamma\mapsto\dot\Gamma B\) has rank \(4\), while

\[
S=\{B:\operatorname{row}(C_{\rm cross})\subseteq\operatorname{row}(B)\}
  =\{TC_{\rm cross}:T\in GL_2\}
\]

has dimension \(4\) in the six-dimensional \(B\)-space, so \(\nu=2\).

**[Exact transverse model]**

\[
H(w)\asymp
\int_{\mathbb R^6}(w+|t|^2)^{-c'}\,dt
\asymp w^{3-c'}\qquad(c'>3).
\]

Consequently,

\[
\boxed{\beta=c'-3}.
\]

Thus

\[
c'=4:\quad \beta=1,
\qquad
c'=4.49:\quad \beta=1.49.
\]

At \(c'=3\) the growth is logarithmic; for \(c'<3\), \(\beta=0\).

**[Necessary feasibility assumption]** This power law requires \(N\) to meet the cubes cleanly—for example, to contain an interior point. “Generic” does not ensure this because the boxes fix a scale. If \(N=\varnothing\), compactness gives a positive minimum loss and \(H(w)\to H(0)<\infty\), so \(\beta=0\).

### Determinant check

**[Exact]** Every \(B\in S\) has rank \(2\), but \(\det(BB^T)\) is **not** bounded away from zero on all of \(S\). For example,

\[
B_\varepsilon=\lambda\operatorname{diag}(1,\varepsilon)C_{\rm cross}
\]

lies in the \(A_{\rm cor}\)-box for sufficiently small fixed \(\lambda\), while
\(\det(B_\varepsilon B_\varepsilon^T)\to0\).

It is, however, uniformly bounded away from zero on the actual exact-fit locus \(N\). There,

\[
\det(BB^T)
=\frac{\det(C_{\rm cross}C_{\rm cross}^T)}{\det(\Gamma)^2}
\ge \frac{\det(C_{\rm cross}C_{\rm cross}^T)}4,
\]

because \(|\det\Gamma|\le2\) on the Gamma cube.

## Q-B

**[Exact]** The coupled integral is finite for every \(w>0\), despite \(Ch=+\infty\). Under feasible clean exact fit it still diverges as \(w\downarrow0\), but only as

\[
H(w)\asymp w^{-(c'-3)}.
\]

The mechanisms are:

- \(w>0\) is the pointwise cutoff.
- The row-space residual supplies the additional \(A_{\rm cor}\)-codimension \(\nu=2\).
- Full-rank \(C_{\rm cross}\) together with bounded \(\Gamma\) excludes ill-conditioned \(B\) from the low-loss region. The row-space residual alone does not do this: it vanishes for \(B_\varepsilon\) above, but cancellation would require \(\Gamma=-\lambda^{-1}\operatorname{diag}(1,\varepsilon^{-1})\), outside the cube.

Therefore

\[
\boxed{c'-\beta=3},
\]

which is more than \(ab/2=2\): the extra reduction is \(\nu/2=1\). It is therefore at least \(1\); under direct additive threshold bookkeeping, \(3.5\) would be lifted by \(3\), to \(6.5\). No numerical heuristic is used.