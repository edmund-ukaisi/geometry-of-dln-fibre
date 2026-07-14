The true rank \(\rho_Z\), not the row dimension \(M_2\), controls both questions.

## Q1 — exact corank weight

Let \(m=M_2\), \(r=\rho_Z\), and factor

\[
Z=BC,
\]

where \(B\in\mathbb R^{m\times r}\) has full column rank and \(C\in\mathbb R^{r\times M_{\rm last}}\) has full row rank. Put \(X=A_{\rm cor}B\). Then

\[
(A_{\rm cor}Z)(A_{\rm cor}Z)^T=X(CC^T)X^T.
\]

The map \(A_{\rm cor}\mapsto X\in\mathbb R^{b\times r}\) is surjective, with a passive kernel of dimension \(b(m-r)\). Those kernel variables do not improve integrability.

### Exact fact

For \(a>0\):

\[
\boxed{
W_{\rm enn}(Z;a,b)<\infty
\iff
b\le r\ \text{and}\ a<r-b+1.
}
\]

For integral \(a,b\), this is equivalent to

\[
\boxed{a+b\le \rho_Z.}
\]

It is not \(a+b\le M_2\). If \(b>r\), the Gram determinant is identically zero.

At a generic rank-\((b-1)\) matrix \(X\), write \(u\) for the component of the last row orthogonal to the first \(b-1\) rows. Then

\[
u\in\mathbb R^{r-b+1},
\qquad
\det(X(CC^T)X^T)=h\,|u|^2,
\]

where \(h\) is smooth and bounded above and below by positive constants. Hence the local integral is

\[
\int_{|u|<\varepsilon}|u|^{-a}\,du
\asymp
\int_0^\varepsilon t^{\,r-b-a}\,dt.
\]

The singular locus therefore has codimension

\[
\boxed{r-b+1=\rho_Z-b+1},
\]

and equality \(a=r-b+1\) gives logarithmic divergence. Gram–Schmidt integration shows that lower-rank strata impose no stronger condition.

### Verdict for \(M=(2,3,3,2)\)

Here \(r=b=2\), so the codimension is \(1\). Moreover,

\[
\det(XHX^T)=\det(H)(\det X)^2,
\]

and for \(a=1\) the integrand is locally \(|s|^{-1}\) transverse to the rank-one hypersurface. Thus

\[
\boxed{W_{\rm enn}(Z;1,2)\text{ is logarithmically divergent}.}
\]

The two kernel coordinates coming from \(M_2-r=1\) per row remain free and do not change codimension.

## Q2a — scaled corank weight

The exact condition is

\[
\boxed{\theta a<\rho_Z-b+1,}
\]

not \(\theta a<M_2-b+1\).

For the concrete instance,

\[
\theta<1.
\]

Thus every \(\theta\in[0,1)\) works, while \(\theta=1\) is the logarithmic endpoint.

## Q2b — coupled sector

Here

\[
\frac{\minAdm(1,3,2)}2=1,
\qquad
\frac{ab}{2}=1.
\]

The pivot-energy condition is

\[
c'-\theta<1
\iff
\theta>c'-1.
\]

Combining it with \(0\le\theta<1\), the admissible interval is

\[
\boxed{\theta\in[0,1)\cap(c'-1,\infty).}
\]

Equivalently,

\[
\begin{cases}
[0,1), & c'<1,\\
(0,1), & c'=1,\\
(c'-1,1), & 1<c'<2.
\end{cases}
\]

This interval is nonempty for every \(c'<2\). Therefore, under the stated interpolation majorant,

\[
\boxed{\text{the coupled sector is finite for every }c'<2.}
\]

For fixed \(\theta<1\), the reachable range is \(c'<1+\theta\); hence

\[
\boxed{\sup_{\theta<1}(1+\theta)=2=\frac{\minAdm(M)}2.}
\]

The supremum equals the RLCT threshold but is not attained by this interpolation at \(c'=2\).

The second test \(M=(2,4,4,3)\) behaves identically: its decoupled weight is logarithmically divergent at \(\theta=1\), while \(\theta<1\) reaches every \(c'<3\), with supremum \(3\).