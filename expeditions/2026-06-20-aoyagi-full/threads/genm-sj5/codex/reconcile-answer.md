## Q1. Different mechanisms, not a contradiction

**Derived.** Route A integrates \(\Gamma\) conditionally and emits two separate singular factors,

\[
\det(Q_bQ_b^\top)^{-a/2}\,
w^{-(c'-ab/2)}.
\]

Its conclusion is specific: these emitted factors both depend on \(A_2\), so they cannot subsequently be treated as independent reduced-chain integrals. The zero-slack cut also prevents repairing this by Hölder.

Route B never emits those factors. Writing the singular values of \(Q\) as \(s_1\ge s_2\ge s_3\), orthogonal rotation of the \(A_0\)-box gives, up to fixed ball-enclosure constants,

\[
g(Q)\asymp
\int_{\text{fixed box}}
\left(s_1^2\|z_1\|^2+s_2^2\|z_2\|^2+s_3^2\|z_3\|^2\right)^{-c'}dz,
\qquad z_i\in\mathbb R^3.
\]

The box is crucial: the collapsing \(z_i\) remain \(O(1)\). In the critical range \(3<c'<7/2\), put \(\eta=2c'-6\in(0,1)\). Beta integration gives

\[
\begin{aligned}
s_2\asymp1 &: \quad g(Q)\asymp s_3^{-\eta},\\
s_1\asymp1,\quad s_3\le s_2\ll1
&:\quad g(Q)\asymp s_2^{-3}s_3^{-\eta}.
\end{aligned}
\]

Thus Route B genuinely removes the particular \(w\times\det\)-Gram factorization created by Route A. But it replaces it by a joint singular-value pushforward problem.

**Verdict.** The routes address different mechanisms. They contradict only if Route B additionally claims that front-first integration makes the remaining deep variables independent. It does not.

## Q2. The global disjoint-\(A_2\) claim is false

**Derived verdict: \(A_2\) remains globally shared.**

The pointwise weighted AM–GM inequality is valid without independence:

\[
\Bigl(\sum_i u_i^2U_i\Bigr)^{-c'}
\le \prod_i (u_i^2U_i)^{-w_ic'}.
\]

What fails is the next step,

\[
\int\prod_i U_i^{-w_ic'}\,dA'
\stackrel{\text{invalid}}{=}
\prod_i\int U_i^{-w_ic'}\,dA'_i.
\]

For \(Q=A_1A_2\),

\[
QQ^\top=A_1(A_2A_2^\top)A_1^\top,
\]

so all collapsing singular directions use the same Gram matrix \(A_2A_2^\top\). Likewise Cauchy–Binet gives

\[
(\wedge^2Q)_{I,J}
=\sum_K(\wedge^2A_1)_{I,K}(\wedge^2A_2)_{K,J},
\]

with the same \(A_2\)-minors appearing in many sums. This is a coupled compound matrix, not independent Wishart blocks.

There is one limited exception. For a fixed invertible basis

\[
M=\begin{bmatrix}w_1\\w_2\\\bar v\end{bmatrix},
\]

the map

\[
A_2\longmapsto (w_1A_2,w_2A_2,\bar vA_2)
\]

does split the \(12\) entries into \(8+4\) coordinates. But its Jacobian is

\[
|\det M|^4
\]

(up to the other scalar units). Hence the inverse change of variables contributes \(|\det M|^{-4}\). The relevant corank cells include \(\det M\to0\), and this factor is nonintegrable across a generic determinant hypersurface. Thus the clean split works only on a quantitative sector \(|\det M|\ge\varepsilon\); its complement needs another rank descent.

The corank-two product locus makes this concrete. Its codimension-four tube has at least the competing profiles

\[
\operatorname{rank}A_1\le1,
\]

and

\[
\operatorname{rank}A_1=\operatorname{rank}A_2=2,
\qquad \ker A_1\subset\operatorname{im}A_2.
\]

No single decomposition into fixed, disjoint rows of \(A_2\) describes both.

There is also an exact obstruction to a symmetric Cauchy–Binet majorant. To dominate

\[
s_2^{-3}s_3^{-\eta}
\]

by \((s_2s_3)^{-b}\), one needs

\[
b\ge\frac{3+\eta}{2}=c'-\frac32>\frac32.
\]

But the \(s_3\)-tube has exponent \(D_1=1\), so integrability of that symmetric majorant requires \(b<1\). There is no overlap.

**Conclusion.** Integrating \(w\) jointly dissolves Route A’s particular emitted-factor coupling, but not the underlying shared-\(A_2\) geometry. It resurfaces as correlated singular values and rank flags. Route B may use a joint flag-tube proof instead of the same decorated ledger, but it cannot use independent deep-block Wisharts globally.

## Q3. \(\{w=0\}\) is not an obstruction by itself, but nullity alone is not the proof

**Derived.** The local model explains the issue exactly:

\[
\int_{\mathbb R^3_v}\int_{\mathbb R^4_\Gamma}
(\|v\|^2+\|\Gamma\|^2)^{-c'}\,d\Gamma\,dv<\infty
\iff 2c'<7.
\]

For \(c'\ge2\), the conditional \(\Gamma\)-integral at \(v=0\) is \(+\infty\), yet the joint seven-dimensional integral is finite for \(c'<7/2\). Thus Route A’s \(+\infty\) fibre over \(w=0\) does not imply divergence of the joint integral.

Under Route B, for fixed \(\operatorname{rank}Q=\rho\),

\[
g(Q)<\infty\iff 2c'<3\rho.
\]

Consequently, for \(3<c'<7/2\), \(g(Q)=+\infty\) on the exact rank-\(\le2\) locus. That locus is null, but its neighbourhood cannot be deleted: its blow-up must be integrated.

The required rank-stratum accounting is

| collapsing singular values | tail tube codim \(D_k\) | stable front dimension \(d_k\) | threshold |
|---|---:|---:|---:|
| \(k=1\) | \(1\) | \(6\) | \((1+6)/2=7/2\) |
| \(k=2\) | \(4\) | \(3\) | \((4+3)/2=7/2\) |
| \(k=3\) | \(8\) | \(0\) | \(4\) |

For corank two, however, the scalar codimensions alone are insufficient. One needs the two-scale flag estimate

\[
\mu\{s_2\le t_2,\ s_3\le t_3\}
\lesssim t_2^3t_3\,\log(e/t_2),
\qquad t_3\le t_2,
\]

or an equivalent resolution. It then gives

\[
\int s_2^{-3}s_3^{-\eta}\,d\mu
\lesssim
\int_0^\kappa\int_0^{s_2}
s_2^{-1}s_3^{-\eta}\log(e/s_2)\,ds_3\,ds_2
<\infty
\iff \eta<1,
\]

namely \(c'<7/2\).

Knowing only the marginal bounds \(s_2^4\) and \(s_3\) does not imply this: their intersection bound is merely \(\min(t_2^4,t_3)\), whose dyadic summation closes only for \(\eta<1/4\), far short of \(\eta<1\).

**Verdict.** Front-first joint integration handles the \(w=0\) fibre through transverse volume, not by simply deleting a null set. The strict threshold plus a sharp joint product-rank flag-tube theorem genuinely closes it. Strictness plus the scalar codimension \(D\) alone does not.

## Q4. Verdict

**Derived verdict.** Route B as advertised does not close. Its claimed global disjoint-\(A_2\)/product-Wishart step is false. The hard part has been moved into the missing joint singular-value flag estimate.

A corrected Route B is legitimate:

\[
\text{front Beta integral}
\;+\;
\text{three corank cells}
\;+\;
\text{joint flag-tube estimates}.
\]

For this single \((3,3,3,4)\) integral it could be shorter than a width-general decorated ledger, but only after proving that flag-tube theorem. Cauchy–Binet measurability and algebraic codimension do not supply it.

Therefore, with the stated bank:

- Route A is the presently robust closing mechanism.
- Route B is not yet a cheaper contained cover plus independent Wishart base.
- Route B avoids Route A’s specific \(w\)-determinant ledger, but relocates the mountain-core into a spectral/rank-flag resolution of the shared \(A_2\) pushforward.