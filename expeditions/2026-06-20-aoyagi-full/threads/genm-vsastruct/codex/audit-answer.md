The casting is a genuine finiteness-preserving change of variables exactly when the three test directions form a basis and the displayed quadratic identities are exact. It is not generally measure-preserving.

## Q1: Jacobian

Write \(A_2=[a_1\,\cdots\,a_4]\), with \(a_j\in\mathbb R^3\), and set
\[
D=\operatorname{diag}(1,\delta,a_{\rm piv}),\qquad
N=DM.
\]
The casting acts independently on each column:
\[
a_j\longmapsto Na_j.
\]
Thus, up to vectorization convention,
\[
L=I_4\otimes N
\quad\text{or}\quad
L=N\otimes I_4.
\]
Consequently
\[
\det L=(\det N)^4
       =\bigl(\delta a_{\rm piv}\det M\bigr)^4,
\]
and
\[
\operatorname{Jac}(L)
=\left|\delta a_{\rm piv}\det M\right|^4.
\]

Therefore \(L\) is an isomorphism iff
\[
\delta\ne0,\qquad a_{\rm piv}\ne0,\qquad \det M\ne0.
\]
For fixed data, its Jacobian is constant.

If \(M\) is orthogonal, then
\[
\operatorname{Jac}(L)=|\delta a_{\rm piv}|^4.
\]
The scaled casting is orthogonal iff
\[
|\delta|=|a_{\rm piv}|=1.
\]
Merely having \(|\delta a_{\rm piv}|=1\) gives Jacobian \(1\), but not necessarily orthogonality.

For a general basis, the map is not measure-preserving unless the absolute Jacobian is \(1\), but it is finiteness-preserving:
\[
dA_2=\left|\delta a_{\rm piv}\det M\right|^{-4}\,dX\,dZ.
\]

**FACT vs INFERENCE:** FACT—the Jacobian is \(\left|\delta a_{\rm piv}\det M\right|^4\). INFERENCE—none; this is exact linear algebra.

## Q2: parallelepiped versus product box

Let
\[
f(X,Z)=S(\|X\|^2,\|Z\|^2;c')
\]
and \(C=[-1,1]^{12}\). If \(L\) is invertible, change of variables gives, as an equality of extended nonnegative integrals,
\[
J_{\rm literal}
=
\left|\delta a_{\rm piv}\det M\right|^{-4}
\int_{L(C)} f(X,Z)\,dX\,dZ.
\]

The image \(L(C)\) is a bounded parallelepiped. For example,
\[
L(C)\subseteq[-T,T]^{12}
\]
whenever
\[
T\ge
\max\bigl\{
\|w_1\|_1,\,
|\delta|\|w_2\|_1,\,
|a_{\rm piv}|\|\bar v\|_1
\bigr\}.
\]
Since \(f\ge0\),
\[
J_{\rm literal}
\le
\left|\delta a_{\rm piv}\det M\right|^{-4}J_{\rm clean}(T).
\]
Hence the domain mismatch does not affect finiteness.

One correction: near \(c'=7/2\), \(S\) is not finite only away from the origin. In fact,
\[
S(0,U_1;c')<\infty\iff c'<\frac32,
\qquad
S(U_0,0;c')<\infty\iff c'<2.
\]
Thus it is infinite on coordinate axes in the near-critical range. Those axes are ambient null sets, and the box-enclosure argument remains valid. Under a singular casting, however, the image can lie in such exceptional geometry, which is exactly why ambient clean integrability no longer suffices.

**FACT vs INFERENCE:** FACT—nonnegative integral monotonicity gives the displayed bound. INFERENCE—the Lean follow-on must instantiate the clean lemma at a sufficiently large \(T\); this is routine if the lemma is available for arbitrary \(T>0\).

## Q3: singular casting and quadratic fidelity

Let
\[
r_0=\operatorname{rank}\!\begin{bmatrix}w_1\\w_2\end{bmatrix},
\qquad
r_1=\operatorname{rank}(\bar v),
\qquad
r=\operatorname{rank}M.
\]
Because the same row map is applied to four columns,
\[
\operatorname{codim}\{U_0=0\}=4r_0,\qquad
\operatorname{codim}\{U_1=0\}=4r_1,
\]
while
\[
\operatorname{codim}\{U_0=U_1=0\}=4r.
\]

Thus \(M\) singular does not necessarily reduce both individual codimensions. For example, if \(w_1,w_2\) are independent but \(\bar v\in\operatorname{span}(w_1,w_2)\), then
\[
(d_0,d_1,d_{01})=(8,4,8),
\]
rather than the clean transverse values \((8,4,12)\).

Ambient \(12\)-dimensional integrability cannot control the restriction of \(f\) to a lower-dimensional image. A concrete counterexample is
\[
w_1=w_2=\bar v=e_1.
\]
Writing \(q=\|e_1A_2\|^2\),
\[
U_0=(1+\delta^2)q,\qquad U_1=a_{\rm piv}^2q,
\]
and homogeneity gives
\[
S(U_0,U_1;c')
=q^{-c'}S(1+\delta^2,a_{\rm piv}^2;c').
\]
Therefore
\[
J_{\rm literal}\ \text{contains}\ 
\int_{\mathbb R^4}\|x\|^{-2c'}\,dx,
\]
which diverges for \(c'\ge2\), even though \(J_{\rm clean}<\infty\) for \(c'<7/2\).

Conversely, singularity does not automatically imply divergence. For
\[
w_1=e_1,\qquad w_2=e_2,\qquad \bar v=e_1,
\]
one has, after naming the first two rows \(z,y\),
\[
u_0^2U_0+u_1^2U_1
\ge C\bigl(u_0^2\|y\|^2+u_1^2\|z\|^2\bigr).
\]
Weighted AM–GM is integrable provided some \(\theta\) satisfies
\[
\theta c'<2,\qquad (1-\theta)c'<\frac32,
\]
which is possible precisely for \(c'<7/2\). This singular case remains finite, but requires a separate argument—not the isomorphic casting.

For the displayed definitions there are exactly no cross-terms:
\[
U_0=\|(w_1A_2,\delta w_2A_2)\|_{\mathbb R^8}^2,
\qquad
U_1=\|a_{\rm piv}\bar vA_2\|_{\mathbb R^4}^2.
\]
If the actual post-reduction units differ, the clean lemma remains applicable if one proves uniform lower comparisons
\[
U_0(A_2)\ge m_0\|X\|^2,\qquad
U_1(A_2)\ge m_1\|Z\|^2
\]
with \(m_0,m_1>0\). Positive-definite within-block cross-terms can be whitened by another constant linear isomorphism. Semidefinite forms, vanishing units, or cross-terms allowing cancellation require a new rank/coercivity argument.

**FACT vs INFERENCE:** FACT—the stated assumptions \(\delta,a_{\rm piv}\ne0\) alone do not imply \(\det M\ne0\), and clean integrability does not control singular pullbacks. INFERENCE—calling invertibility a “benign chart hypothesis” is justified only if the preceding chart construction explicitly proves it.

## Verdict

The follow-on is a genuine constant-Jacobian, finiteness-preserving change of variables—not generally a measure-preserving one—provided that:

- \(\det[w_1;w_2;\bar v]\ne0\);
- \(\delta,a_{\rm piv}\ne0\);
- the displayed norm identities are exact, or suitable positive coercive comparisons are proved;
- the image parallelepiped is enclosed in a box covered by the clean lemma;
- if these coefficients vary over outer variables, the reciprocal Jacobian and comparison constants are controlled uniformly or shown separately integrable.

Without the basis/coercivity hypotheses, the casting is a hidden load-bearing gap. Nonzero pivot scalars alone do not close it.