Let \(M=M_2\) and define, canonically,
\[
R=(AA^\top)^{1/2},\qquad Q=R^{-1}A.
\]
Then \(A=RQ\), \(R\) is invertible, and \(QQ^\top=I_b\).

## Exact \(A\)-dependence

For every \(S\),
\[
(AS)(AS)^\top
=R(QS)(QS)^\top R^\top,
\]
so
\[
\det((AS)(AS)^\top)
=\det(AA^\top)\det((QS)(QS)^\top).
\]
Consequently,
\[
\boxed{
I(A)=\det(AA^\top)^{-a/2}\,C(Q)
}
\]
where
\[
C(Q)=\int_{[-1,1]^{M\times n}}
\det((QS)(QS)^\top)^{-a/2}\,dS.
\]

Thus all singular values of \(A\) enter only through \(\det(AA^\top)\). There is no additional condition-number dependence. The factor \(C(Q)\) depends only on the orientation of the row space of \(A\).

However, \(C(Q)\) is not generally identical for all \(Q\), because the cube is not rotationally invariant.

For example, with \(b=1,M=2,n=2,a=1\), put
\[
q_1=(1,0),\qquad q_2=2^{-1/2}(1,1).
\]
Writing \(L=\log(1+\sqrt2)\), direct integration gives
\[
C(q_1)=32L\approx28.20,
\]
whereas
\[
C(q_2)=32\sqrt2\left(L+\frac{1-\sqrt2}{3}\right)
\approx33.64.
\]
So the literal formula with one \(Q\)-independent constant is false. What is true—and sufficient—is uniform two-sided comparability.

## Uniformity over \(Q\)

Let \(d=M-b\). The pushforward of Lebesgue measure on the cube under \(s\mapsto Qs\) has density
\[
f_Q(x)
=\mathcal H^d\bigl([-1,1]^M\cap\{s:Qs=x\}\bigr),
\]
because \(\sqrt{\det(QQ^\top)}=1\).

Every such section lies inside an affine \(d\)-ball of radius \(\sqrt M\). Hence
\[
f_Q(x)\le L_{M,b}:=\omega_d M^{d/2},
\qquad
\operatorname{supp}f_Q\subseteq B_{\sqrt M}^b,
\]
uniformly over all orthonormal-row \(Q\).

There is also a uniform lower bound near zero. If \(|x|\le \tfrac12\), then
\[
Q^\top x+\{z\in\ker Q:|z|\le\tfrac12\}\subset[-1,1]^M,
\]
so
\[
f_Q(x)\ge \ell_{M,b}:=\omega_d2^{-d}.
\]

Writing \(X=[x_1,\ldots,x_n]\),
\[
C(Q)=\int
\det(XX^\top)^{-a/2}\prod_{j=1}^n f_Q(x_j)\,dx_1\cdots dx_n.
\]
Therefore
\[
\ell_{M,b}^{\,n}K_{1/2}
\le C(Q)\le
L_{M,b}^{\,n}K_{\sqrt M},
\]
where
\[
K_r=\int_{(B_r^b)^n}\det(XX^\top)^{-a/2}\,dX.
\]

This density estimate—not compactness of the Stiefel manifold alone—is the reason for uniformity.

## Basic matrix-integrability lemma

For a \(b\times N\) matrix \(Y\), the function
\[
\det(YY^\top)^{-a/2}
\]
is locally integrable exactly when
\[
\boxed{a<N-b+1.}
\]

Indeed, if \(y_1,\ldots,y_b\in\mathbb R^N\) are the rows and
\[
V_{i-1}=\operatorname{span}(y_1,\ldots,y_{i-1}),
\]
Gram–Schmidt gives, off a null set,
\[
\det(YY^\top)
=\prod_{i=1}^b
\operatorname{dist}(y_i,V_{i-1})^2.
\]
The normal space to \(V_{i-1}\) has dimension \(N-i+1\), and
\[
\int_{|z|<\varepsilon}|z|^{-a}\,dz<\infty
\quad\Longleftrightarrow\quad
a<N-i+1.
\]
The most restrictive step is \(i=b\), giving \(a<N-b+1\). If equality or the reverse holds, integration transverse to a rank-\((b-1)\) matrix diverges; equality is logarithmic.

No Cauchy–Binet expansion is involved.

## Inner and outer thresholds

Applying the lemma with \(N=n\),
\[
\boxed{
C(Q)<\infty\ \text{uniformly in }Q
\iff a<n-b+1.
}
\]
For integer \(a,b,n\), this is
\[
\boxed{a+b\le n.}
\]

Applying the same lemma to \(A\in\mathbb R^{b\times M}\),
\[
\boxed{
\int_{[-1,1]^{b\times M}}
\det(AA^\top)^{-a/2}\,dA<\infty
\iff a<M-b+1,
}
\]
or, for integers,
\[
\boxed{a+b\le M.}
\]

Hence
\[
\boxed{
\iint
\det((AS)(AS)^\top)^{-a/2}\,dA\,dS<\infty
\iff
a+b\le\min(M_2,n).
}
\]

Necessity is also clean: if the inner condition fails, \(I(A)=\infty\) for every full-rank \(A\); if only the outer condition fails, the uniform positive lower bound on \(C(Q)\) prevents any compensation.

## Worked case

For
\[
b=2,\quad a=1,\quad M_2=n=4,
\]
both inner and outer normal codimensions at the worst rank stratum equal
\[
4-2+1=3>1.
\]
Thus
\[
I(A)=\det(AA^\top)^{-1/2}C(Q),
\qquad
0<c\le C(Q)\le C<\infty,
\]
and the double integral is finite since \(a+b=3\le4\).

**Verdict: CLEAN two-step.** The orientation factor \(C(Q)\) is generally nonconstant, but it is uniformly bounded above and below. There is no singular-value coupling and no recursion is required. All statements above are proved, not conjectured.