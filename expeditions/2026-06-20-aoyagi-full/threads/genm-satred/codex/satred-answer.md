Let
\[
n=M_2,\qquad p=M_3,\qquad k=u+b.
\]
The decisive identity is
\[
W=Pz_0+B_{12}A_{\rm cor}
=
\underbrace{[\,P\ \ B_{12}\,]}_{C\in\mathbb R^{u\times k}}
\underbrace{\binom{z_0}{A_{\rm cor}}}_{D\in\mathbb R^{k\times n}}.
\]
Since excluding \(\det P=0\) removes a null set, \(I(c')\) is exactly the integral for the three-matrix product \(CDz_1\).

## Q1. Exact threshold

Define
\[
m_2(s,n,p)
=
\min_{0\le r\le\min(s,n)}
\bigl((s-r)(n-r)+rp\bigr).
\]
Thus the given reduced codimension is \(m=m_2(u,n,p)\).

The exact codimension for the inserted chain is
\[
m_I
=
\min_{0\le s\le u}
\left[
(u-s)(k-s)+m_2(s,n,p)
\right].
\]
Equivalently,
\[
m_I
=
\min_{\substack{0\le s\le u\\0\le r\le\min(s,n)}}
\left[
(u-s)(u+b-s)+(s-r)(n-r)+rp
\right].
\]

Then
\[
\boxed{\quad I(c')<\infty\iff c'<\frac{m_I}{2}.\quad}
\]
It diverges at \(c'=m_I/2\) and above.

This follows from the determinantal rank-sector resolution for the matrix chain:
\[
\operatorname{Vol}\{\|CDz_1\|<\varepsilon\}
=
\varepsilon^{m_I}
(\log(1/\varepsilon))^{O(1)}.
\]
Layer-cake integration then gives the stated threshold. This is a special matrix-chain result; it is not the generally false assertion that every squared polynomial map has RLCT equal to half the zero-set codimension.

Since the choice \(s=u\) recovers \(m\),
\[
m_I\le m.
\]
Equality holds exactly when
\[
j(b+j)+m_2(u-j,n,p)\ge m
\qquad(1\le j\le u).
\]
In particular, \(b\ge\min(n,p)-1\) is sufficient for \(m_I=m\), but not necessary.

Strict drop example:
\[
u=1,\quad b=1,\quad n=p=3.
\]
Here
\[
m=3,\qquad m_I=2,
\]
so
\[
R(c')<\infty\quad(c'<3/2),
\qquad
I(c')<\infty\quad(c'<1).
\]

Thus the answer is not uniformly “the same threshold”: it depends on the widths.

## Q2. The determinant divergence

The factor
\[
\int |\det P|^{-n}\,dP=\infty
\]
is an artifact of enlarging the conditional \(W\)-domain.

At fixed \(P,B_{12},A_{\rm cor}\), the actual image is
\[
B_{12}A_{\rm cor}+P[-1,1]^{u\times n}.
\]
Its volume is
\[
2^{un}|\det P|^n.
\]
The conditional density has height \(|\det P|^{-n}\), but its support collapses with precisely the compensating volume \(|\det P|^n\). Replacing that collapsing parallelepiped by a fixed box destroys this cancellation.

Nevertheless, a genuine divergence can remain for a different reason: the whole matrix
\[
C=[\,P\ B_{12}\,]
\]
can approach a lower-rank matrix. That is the extra-layer mechanism responsible for \(m_I<m\). Therefore:

- the naked determinant factor is spurious;
- a threshold drop, when it occurs, is genuine and is caused by rank degeneration of \(C\), not by the invalid enlarged-domain estimate.

## Q3. Pushforward density

Let \(\rho\) be the density of \(W=CD\). Put
\[
q=\min(u,n).
\]
Near an interior point \(W_0\) of rank \(r<q\), use normal coordinates transverse to the rank-\(r\) stratum. Along a balanced transverse ray \(W=W_0+\varepsilon V\), define
\[
h=q-r,\qquad d_r=n-r-b,
\]
and
\[
E_j=j(b-n+r+j)=j(j-d_r),
\qquad 0\le j\le h.
\]
Then the leading transverse exponent is
\[
E_*=\min_{0\le j\le h}E_j.
\]

More explicitly:

- If \(b\ge n-r\), then \(\rho\) is bounded near the rank-\(r\) stratum.
- If \(b=n-r-1\), then
  \[
  \rho\asymp \log(1/\varepsilon).
  \]
- If \(b\le n-r-2\), then
  \[
  \rho\asymp \varepsilon^{E_*},
  \qquad E_*<0,
  \]
  with one additional logarithm when two adjacent \(E_j\)'s attain the minimum.

This comes from the matrix-Bessel/Wishart representation
\[
\rho_G(V)
\asymp
\int_{S>0}
(\det S)^{(b-n+r-1)/2}
e^{-\frac12(\operatorname{tr}S+
\operatorname{tr}(G(V)S^{-1}))}\,dS
\]
for Gaussian factors. Restricting to compact interior factor charts gives the same powers and logarithms for the box law.

At \(W=0\), let \(d=n-b\). Then:

- \(b\ge n\): \(\rho\) is bounded.
- \(b=n-1\): \(\rho(W)\asymp\log(1/\|W\|)\).
- \(b\le n-2\):
  \[
  \rho(W)
  \asymp
  \|W\|^{-A}
  \bigl(\log(1/\|W\|)\bigr)^\eta,
  \]
  where
  \[
  A=\max_{1\le j\le\min(u,n)}j(n-b-j).
  \]

For \(u\ge n\),
\[
A=\left\lfloor\frac{(n-b)^2}{4}\right\rfloor.
\]
For \(u<n\), the maximum is truncated at \(j=u\). The logarithm \(\eta=1\) occurs at the adjacent-minimizer resonance.

Consequences by regime:

- \(u<n\): already the generic rank-\((u-1)\) locus can be singular:
  \[
  \rho\asymp
  \begin{cases}
  \operatorname{dist}^{\,b-n+u},&b<n-u,\\
  \log(1/\operatorname{dist}),&b=n-u,\\
  O(1),&b>n-u.
  \end{cases}
  \]
- \(u=n\): \(\rho\) is bounded along the generic hypersurface \(\det W=0\) for every \(b\ge1\); blow-up occurs only at deeper ranks.
- \(u>n\): likewise, the generic rank-\((n-1)\) stratum is bounded; only deeper rank strata may blow up.

Globally, \(\rho\) is bounded precisely when \(b\ge n\).

The weighted integral therefore has threshold \(m_I/2\), not automatically \(m/2\). If \(m_I=m\), every strict \(c'<\mathrm{thr}\) is allowed; no additional loss in the threshold occurs. The endpoint \(c'=\mathrm{thr}\) still diverges. Logarithmic density bounds may require choosing a little headroom in a proof, but they do not alter the exponent. Power singularities can alter it.

In the strict example \((u,b,n,p)=(1,1,3,3)\),
\[
\rho(W)\asymp\|W\|^{-1}\qquad(W\in\mathbb R^3).
\]
Taking \(z_1\) in an open set of invertible matrices gives
\[
\int_0^\varepsilon
r^{2}\,r^{-1}\,r^{-2c'}\,dr,
\]
whose threshold is \(c'=1\), exactly \(m_I/2\).

## Q4. Determinant cutoff

On \(\{|\det P|\ge\delta\}\),
\[
|\det P|^{-n}\le\delta^{-n}.
\]
Hence the original substitution and fixed-box enlargement give immediately
\[
I_{\ge\delta}(c')
\le C_\delta R(c')<\infty
\qquad(c'<\mathrm{thr}).
\]
For a nonempty cutoff region of positive measure, its exact threshold is the reduced threshold \(\mathrm{thr}\).

For the full integral:

- If \(c'<m_I/2\), then \(F^{-c'}\in L^1\), so dominated convergence gives
  \[
  \int_{\{0<|\det P|<\delta\}}F^{-c'}\longrightarrow0.
  \]
  Thus there is no nonzero limiting mass at singular \(P\), although the decay can be slow.
- If \(m_I/2\le c'<\mathrm{thr}\) in a strict-drop case, every determinant-cutoff integral is finite, but the omitted near-singular region carries the genuine divergence.

## Fully explicit scalar check

Take \(u=n=b=p=1\), and write
\[
w=px+qa,\qquad F=|wy|^2.
\]
The unnormalised density of one product \(px\) is
\[
f(t)=2\log(1/|t|)\mathbf 1_{\{0<|t|<1\}}.
\]
Therefore
\[
\rho=f*f.
\]
Since \(f\in L^2\),
\[
\rho(w)\le\|f\|_2^2=16,
\qquad
\rho(0)=16.
\]
Consequently,
\[
I(c')
=
\left(\int_{-1}^1|y|^{-2c'}dy\right)
\left(\int_{-2}^2|w|^{-2c'}\rho(w)\,dw\right),
\]
and both factors are finite exactly when
\[
\boxed{c'<\tfrac12}.
\]

Here \(m_I=m=1\). The fake \(|p|^{-1}\) is canceled by the true conditional interval length \(2|p|\). Moreover, with \(s=2c'<1\),
\[
\int_{\{0<|p|<\delta\}}F^{-c'}
=
\frac{32}{(1-s)^3}\delta+o(\delta),
\]
so the near-singular-\(p\) mass vanishes linearly.