## Q1

**PROVEN — the nested-qbox recursion does not converge universally.**

Put \(k=M_1-s\), \(r=M_0-s\), and \(n_1=M_2,n_2=M_3,\ldots\). Successive qboxes require

\[
k\le n_1,\qquad r<n_1-k+1,
\]

then, for \(j\ge1\),

\[
n_j\le n_{j+1},\qquad n_{j-1}<n_{j+1}-n_j+1,
\]

where \(n_0=k\). Since dimensions are integral, these are the Fibonacci-type inequalities

\[
r+k\le M_2,\qquad k+M_2\le M_3,\qquad
M_2+M_3\le M_4,\ldots
\]

They are not consequences of the minAdm charge recursion. If the remaining tail has generic rank \(\rho<M_{j+1}\), its effective qbox dimension is \(\rho\), making the condition still stricter; the ordinary Gram determinant is then identically zero.

The smallest positive-width hard cell is

\[
M=(2,2,1,2),\qquad u=s=1,\qquad a=b=d=r=k=1.
\]

Indeed,

\[
\minAdm(2,2,1,2)
 =\min\{4,\ 1+\minAdm(1,1,2),\ \minAdm(2,1,2)\}
 =\min\{4,2,2\}=2.
\]

Thus \(s=1\) is binding, with source charge \(rk=1\) and reduced charge

\[
\minAdm(1,1,2)=1.
\]

The charge bookkeeping reaches \(1+1=2\) exactly, but the first \(C\)-qbox has

\[
(b_{\rm box},q_{\rm box},a_{\rm box})=(k,M_2,r)=(1,1,1),
\]

and requires \(1<1-1+1=1\), which is false. It diverges logarithmically. Consequently the route fails throughout the hard window \(1/2<c'<1=\minAdm(M)/2\).

This cell has minimum total width \(7\); \(M=(2,2,1,1)\) has no binding positive-charge residual stratum.

## Q2

**PROVEN — a free \(C\) makes the step legitimate only conditionally.**

For positive-definite \(G=ZZ^{\mathsf T}\), the substitution \(X=CG^{1/2}\) gives the bound

\[
\int_{C\text{-box}}\det(CGC^{\mathsf T})^{-r/2}\,dC
\le K\,\det(G)^{-k/2}
\]

exactly when \(k\le M_2\) and \(r<M_2-k+1\). The displayed equality with a \(G\)-independent box constant is not literal: the substitution transforms the box into a \(G\)-dependent parallelepiped. The required upper comparison is valid because that image lies in a uniform bounded box.

A carried product-Gram is not automatically forbidden if the next free layer is integrated immediately and its qbox converges. That is direct iterated qbox reasoning, not an appeal to plain \(hIH\). But if the next qbox fails, the carried weight is precisely the forbidden naked Gram decoration.

For example, at \(M=(2,2,2,2)\), \(s=1\), the first qbox \((1,2,1)\) converges, but it leaves

\[
\det(ZZ^{\mathsf T})^{-1/2}=|\det Z|^{-1},
\qquad Z\in\mathbb R^{2\times2}.
\]

The terminal qbox \((2,2,1)\) requires \(1<1\) and diverges near nonzero rank-one \(Z\).

## Q3

**VERDICT: SECOND-WALL**

**PROVEN.** Exact charge addition does not supply the independent strict qbox inequalities. Closing these cells requires a genuinely coupled source–tail incidence mechanism—retaining the finite-domain cap/joint \((\Delta,C,Z)\) geometry, with the scalar free-bilinear resolution at the minimal cell—not a carried-Gram qbox recursion.

Cheapest discriminating computation: for \(M=(2,2,1,2)\) and any \(z\ne0\),

\[
\int_{-1}^{1}\det\!\bigl((cz)(cz)^{\mathsf T}\bigr)^{-1/2}\,dc
=\|z\|^{-1}\int_{-1}^{1}|c|^{-1}\,dc
=\infty .
\]