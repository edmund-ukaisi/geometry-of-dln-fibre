## Q1 — PROVEN: a direct \(T\leftrightarrow e\) bijection

There is one indexing correction. With \(e_1,\ldots,e_L\), the paper’s QIP is

\[
G(M,e)=\sum_{1\le j\le i\le L}
e_i\bigl(e_j+M_j-M_{j-1}\bigr).
\]

Your \(M_{j+1}-M_j\) version is correct only with zero-based \(e_0,\ldots,e_{L-1}\). Read literally with \(e_1,\ldots,e_L\), it is off by one.

Also, Aoyagi admissibility must include \(T_{L-1}=0\). Introduce \(T_{-1}:=M_0\) and, using zero-based QIP variables, set

\[
\boxed{e_i=T_{i-1}-T_i,\qquad 0\le i<L.}
\]

Thus

\[
e_0=M_0-T_0,\quad e_i=T_{i-1}-T_i\ (i\ge1),
\]

and

\[
\sum_{i=0}^{L-1}e_i=M_0-T_{L-1}=M_0.
\]

The inverse is

\[
\boxed{
T_i=M_0-\sum_{k=0}^{i}e_k
=\sum_{k=i+1}^{L-1}e_k.
}
\]

For weakly increasing \(M\), every feasible \(e\) produces an admissible \(T\): it is decreasing and

\[
T_i\le M_0\le M_{i+1}.
\]

Conversely, every admissible \(T\) produces a feasible \(e\). Hence this is a bijection precisely in the monotone case.

Let \(E_i=\sum_{k=0}^i e_k=M_0-T_i\). Then

\[
\begin{aligned}
Mval(M,T)
 &=\sum_{i=0}^{L-1}e_i(M_{i+1}-T_i)\\
 &=\sum_i e_i(E_i+M_{i+1}-M_0).
\end{aligned}
\]

Meanwhile,

\[
\begin{aligned}
G(M,e)
 &=\sum_i e_i\sum_{j\le i}(e_j+M_{j+1}-M_j)\\
 &=\sum_i e_i(E_i+M_{i+1}-M_0).
\end{aligned}
\]

Therefore

\[
\boxed{Mval(M,T)=G(M,e)}
\]

pointwise under the bijection, and consequently

\[
\boxed{\minAdm(M)=qipMin(M)}
\]

for every weakly increasing \(M\).

For nonmonotone \(M\), the forward map \(T\mapsto e\) still works, but the inverse may violate \(T_i\le M_{i+1}\). Thus the formal nonmonotone QIP minimizes over a strictly larger set:

\[
qipMin(M)\le \minAdm(M),
\]

possibly with negative values. The paper itself applies the QIP only after sorting.

## Q2 — PROVEN: \(\minAdm\) is permutation-invariant by a pure \(\mathbb N\) argument

Let \(F=\minAdm\), and define

\[
(K_bf)(a)
=
\min_{0\le t\le\min(a,b)}
\bigl((a-t)(b-t)+f(t)\bigr),
\qquad B_c(a)=ac.
\]

The layer-peel recursion gives

\[
F(a,m_1,\ldots,m_L)
=
K_{m_1}\cdots K_{m_{L-1}}B_{m_L}(a).
\]

The basic three-width quantity is

\[
H(a,b,c)=K_bB_c(a)
=\min_t\bigl((a-t)(b-t)+ct\bigr).
\]

If \(x\le y\le z\) is the increasing rearrangement of \(a,b,c\), completing the square gives

\[
\boxed{
H(a,b,c)
=
xy-\left\lfloor
\frac{\max(0,x+y-z)^2}{4}
\right\rfloor.
}
\]

Hence \(H\) is symmetric in all three arguments.

More generally,

\[
(K_bK_cf)(a)
=
\min_{0\le s\le\min(a,b,c)}
\bigl(f(s)+H(a-s,b-s,c-s)\bigr),
\]

so \(K_bK_c=K_cK_b\). Moreover \(K_bB_c=K_cB_b\), and the leading two widths may be swapped directly because \((a-t)(b-t)\) is symmetric. Adjacent transpositions therefore give

\[
\boxed{\minAdm(M)=\minAdm(\sigma M)}
\]

for every permutation \(\sigma\).

Thus the clean route is

\[
\boxed{
\minAdm(M)
=\minAdm(M^\uparrow)
=qipMin(M^\uparrow)
=cCodim(M^\uparrow,0)
=cCodim(M,0).
}
\]

There is no genuine alternative “route (b)”: its first equality already requires permutation invariance of \(\minAdm\). The banked permutation invariance of \(cCodim\) supplies only the last equality. The operator proof is independent of geometry, so there is no circularity.

## Q3 — PROVEN for these loci; false for arbitrary real varieties

Let \(X_{\mathbb R}\) be the real zero-product locus and \(X_{\mathbb C}\) its complexification. Then

\[
\boxed{
\dim_{\mathbb R}X_{\mathbb R}
=
\dim_{\mathbb C}X_{\mathbb C},
\qquad
\operatorname{codim}_{\mathbb R}X_{\mathbb R}
=
cCodim(M,0).
}
\]

This is stronger than “the equations are the same.” For these type-\(A\) loci:

- Every realizable rank pattern has a \(0\)-\(1\) partial-permutation representative over \(\mathbb R\).
- Its real orbit is a smooth real manifold whose real dimension equals the algebraic dimension of the corresponding complex orbit.
- The real orbit is Zariski dense in its algebraic orbit closure.
- The product-rank locus is a finite union of such orbit closures.

This is exactly the paper’s base-field theorem and its real-points remark: [main.tex](/home/ubuntu/workspace/geometry-of-dln-fibre/paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:605) and [main.tex](/home/ubuntu/workspace/geometry-of-dln-fibre/paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:860).

Thus every top-dimensional algebraic component contains a top-dimensional smooth real stratum. Real orbits may be disconnected, so the real interpretation of \(\theta\) is subtler, but \(C\) is unchanged.

The general principle “same real equations implies equal real and complex dimensions” is false: \(x^2+y^2=0\) has a one-dimensional complex locus but only the origin over \(\mathbb R\), and real loci can be empty. Those failures do not occur here.

For a bounded neighborhood meeting a top-dimensional real stratum—particularly a neighborhood of the origin, since the zero-product locus is conical—the semialgebraic tube theorem gives

\[
\operatorname{vol}\{x\in B:\operatorname{dist}(x,X_{\mathbb R})\le t\}
=\Theta(t^C).
\]

The whole-space tube has infinite volume, and a localization missing all top-dimensional strata can have a larger local exponent. An actual \(\sim c\,t^C\) statement also requires the usual regular compact localization.

Finally, this is an ordinary Euclidean distance tube. It is not automatically the product sublevel set \(\{\|A_L\cdots A_1\|\le t\}\).

## Q4 — YES for analytic finiteness; \(cCodim\) is not logically needed

If an analytic induction proves

\[
\int_B\|A_L\cdots A_1\|^{-2c}\,dA<\infty
\qquad\text{for }c<\frac{\minAdm(M)}2,
\]

using the layer-peel recursion and a valid volume-preserving reduction to a shorter chain, then \(cCodim\) is not needed for that finiteness result. It is needed only to identify

\[
\minAdm(M)=C
\]

with the paper’s geometric invariant, or to obtain the cheap upper bound \(\mathrm{rlct}\le C/2\).

Two cautions are essential:

1. Finiteness below the threshold alone is not a full tube asymptotic or exact RLCT; one also needs divergence at the threshold or another upper bound.

2. A unit Jacobian preserves volume, but does not by itself identify Euclidean distance tubes. One needs the change of variables to carry the relevant product sublevel sets exactly/comparably; transferring distance requires local bi-Lipschitz control.

Indeed, for

\[
V(r)=\operatorname{vol}\{\|A_L\cdots A_1\|\le r\},
\]

layer-cake gives

\[
\int \|A_L\cdots A_1\|^{-2c}<\infty
\iff
\int_0 r^{-2c-1}V(r)\,dr<\infty.
\]

Logs in \(V(r)\), such as \(r^C\log(1/r)\), do not change this threshold.

So the precise verdict is:

\[
\boxed{\text{\(\minAdm\) is self-sufficient for the analytic finiteness leg.}}
\]

The geometric \(cCodim\) bridge is optional analytically, but required to call that integer the paper’s \(C\), and useful for sharpness via the universal codimension upper bound.