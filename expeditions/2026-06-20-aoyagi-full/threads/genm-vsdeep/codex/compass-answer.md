1. VERDICT: SIDESTEPS coarea — for the original front-first coupled integral, not for the isolated critical Gram weight.

2. Crux argument

- The \(\sigma\)-majorant is obtained after integrating the front box; it is pointwise in \(P\), not in all variables.
- Its proof uses only a fixed-\(P\) orthogonal change of coordinates, Tonelli, and radial power estimates—no non-square coarea.
- It must be rank-stratified: a bound using only \(\sigma_r(P)\) requires \(\sigma_{r-1}(P)\) bounded below.
- At \(2c'=m_0(r-1)\), the bound has a logarithm; the claimed \(O(\sigma_r^0)\) bound is false exactly there.
- A product tube estimate is not intrinsically a coarea fact: it can be proved by determinantal covering plus dyadic induction over factor rank profiles.
- Bare algebraic codimension or one Cauchy–Binet polynomial is insufficient; vanishing order and product incidence must be controlled.
- The literal estimate \(Ct^D\) can fail: tied product-rank components yield \(Ct^D\log(1/t)\).
- This logarithm is harmless for \(\alpha<D\); alternatively use \(C_\varepsilon t^{D-\varepsilon}\).

Scope warning: for fixed full-row-rank \(A\in\mathbb R^{3\times4}\),

\[
\int \det(YAA^\top Y^\top)^{-a/2}\,dY<\infty
\quad\Longleftrightarrow\quad a<2.
\]

Indeed, near \(Y=\begin{psmallmatrix}1&0&0\\u&x&y\end{psmallmatrix}\), the Gram determinant is comparable to \(x^2+y^2\). Thus at the concrete emitted exponent \(a=2\), the isolated Gram weight is logarithmically divergent. Front-first must therefore be applied before emitting that factor, retaining the coupling.

3. Minimal lemma chain

(a) Pointwise front-first majorant — theorem

Let \(P\in\mathbb R^{r\times n}\), with singular values
\(s_1\ge\cdots\ge s_r>0\), and set

\[
G_{c'}(P)=\int_{[-R,R]^{m_0\times r}}\|XP\|_F^{-2c'}\,dX.
\]

On a sector \(s_{r-1}\ge\kappa>0\), assuming \(2c'<m_0r\),

\[
G_{c'}(P)\le C
\begin{cases}
1,&2c'<m_0(r-1),\\
1+\log(1/s_r),&2c'=m_0(r-1),\\
s_r^{-\alpha},&m_0(r-1)<2c'<m_0r,
\end{cases}
\]

where \(\alpha=2c'-m_0(r-1)\). This follows by enclosing the rotated box in a ball and integrating

\[
(\|u\|^2+s_r^2\|v\|^2)^{-c'}
\]

in dimensions \(m_0(r-1)\) and \(m_0\).

For the \((3,3,3,4)\) front integral, \(m_0=r=3\), and the relevant value is \(\sigma_3\), not \(\sigma_4\):

\[
\alpha=\max(0,2c'-6)<1\qquad(c'<7/2),
\]

with a logarithm at \(c'=3\).

(b) Product tube estimate — new custom lemma, but no coarea

For factor-box Lebesgue measure \(\nu\), prove

\[
\nu\{\sigma_r(A_1\cdots A_\ell)\le t\}
 \le C\,t^{D_r}\bigl(\log(e/t)\bigr)^{K_r},
\]

or merely, for every \(\varepsilon>0\),

\[
\nu\{\sigma_r(A_1\cdots A_\ell)\le t\}
 \le C_\varepsilon t^{D_r-\varepsilon}.
\]

Here \(D_r\) is the minimum codimension among factor-rank/incidence profiles producing product rank at most \(r-1\).

Concrete facts:

- For a free \(3\times4\) matrix, \(\operatorname{vol}\{\sigma_3\le t\}\le Ct^2\).
- For \(P=A_1A_2\), \(A_1:3\times3\), \(A_2:3\times4\),

\[
(D_1,D_2,D_3)=(8,4,1).
\]

In particular,

\[
\nu\{\sigma_3(P)\le t\}\le Ct.
\]

This last bound follows elementarily from

\[
\sigma_3(A_1A_2)\ge\sigma_3(A_1)\sigma_3(A_2),
\]

the free-matrix bounds \(O(u)\) and \(O(u^2)\), and a dyadic product sum. For \(\sigma_2\), the two codimension-four profiles tie, so one should allow \(Ct^4\log(e/t)\).

For general products, use finite pivot/rank-profile covers, Grassmannian incidence coverings, and dyadic induction on factor scales. Cauchy–Binet helps identify rank conditions but does not alone prove the sharp exponent.

(c) Radial/tube endpoint — theorem

From the tube bound, dyadic summation gives

\[
\int \sigma_r(P)^{-\alpha}\,d\nu(P)<\infty
\quad\text{when}\quad \alpha<D_r,
\]

because

\[
\int_0^\delta
t^{D_r-\alpha-1}\bigl(\log(e/t)\bigr)^{K_r}\,dt<\infty
\iff \alpha<D_r.
\]

Mathlib plausibility: Tonelli, product Lebesgue measure, orthogonal measure preservation, geometric-series estimates, and one-dimensional power integrability should be available. The sector majorant and especially the sharp product-rank tube lemma are not expected to exist and require custom formalisation.

5. Confidence: 0.86. The verdict would flip if the actual product tail had a sublevel power strictly smaller than \(D_{\rm prod}\), rather than only logarithmic losses.