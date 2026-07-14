[FACT] **Verdict: the target inequality is FALSE as stated.** The \(M=(2,2,3)\) incidence corner is sound and has threshold \(c'=2\), but another permitted configuration has a logarithmically divergent Gram factor while the reduced comparator remains finite.

## Q1 — the \(M=(2,2,3)\) corner

[FACT] Put
\[
x=p+\beta,\qquad \rho=|t|,\qquad y=(\beta,\gamma/\sqrt{1+\rho^2}),\qquad s=|y|.
\]
All omitted Jacobians are analytic units near the origin. The loss becomes
\[
x^2+\rho^2s^2,
\]
and polar coordinates in the two-dimensional \(t\)- and \(y\)-planes give
\[
I(q)\asymp
\int_0^\delta\!\!\int_0^\delta\!\!\int_{-\delta}^{\delta}
(x^2+\rho^2s^2)^{-q}\,\rho s\,dx\,d\rho\,ds.
\]

[FACT] In the chart \(|x|\le \rho s\), write \(x=\rho s\,v\). Its Jacobian is \(dx=\rho s\,dv\), so the monomial density is
\[
\rho^{\,2-2q}s^{\,2-2q}(1+v^2)^{-q}\,d\rho\,ds\,dv.
\]
The complementary chart gives the same exponents, equivalently by the exact fibre estimate
\[
\int_{-\delta}^{\delta}(x^2+A^2)^{-q}dx\asymp A^{1-2q},
\qquad q>\frac12.
\]

[FACT] Thus the decisive radial integrals are
\[
\int_0^\delta \rho^{\,2-2q}\,d\rho
\int_0^\delta s^{\,2-2q}\,ds
=
\int_0^\delta \rho^{\,3-2c'}\,d\rho
\int_0^\delta s^{\,3-2c'}\,ds,
\]
because \(q=c'-\tfrac12\).

[FACT] Both converge exactly when
\[
3-2c'>-1\iff c'<2.
\]
Hence
\[
\boxed{\operatorname{RLCT}_q=\frac32,\qquad \operatorname{RLCT}_{c'}=2=T_1.}
\]

[FACT] At \(c'=2\), both factors are \(\int_0^\delta r^{-1}dr\); the corner has a double logarithmic divergence. For every fixed \(c'<2\), its value is finite, although it blows up like a double pole as \(c'\uparrow2\).

## Q2 — general incidence charts

[FACT] Write \(n=M_2\) and \(d=n-b\), initially assuming \(b\le n\) and \(Q_b\) has full row rank. On a \(b\times b\) minor chart,
\[
Q_b=D[I_b\mid X],\qquad
Q_p=[U\mid UX+W],
\]
where \(D\in GL_b\), \(X\in\mathbb R^{b\times d}\), and \(W\in\mathbb R^{u\times d}\).

[FACT] With
\[
N=\binom{-X}{I_d},
\]
one has \(Q_bN=0\), \(Q_pN=W\), and
\[
\|Q_p(I-\Pi_b)\|_F^2
=\operatorname{tr}\!\left(W(I_d+X^{\mathsf T}X)^{-1}W^{\mathsf T}\right)
\asymp\|W\|_F^2.
\]

[FACT] The precise incidence strata are
\[
\mathcal I_h=\{\dim(\operatorname{row}Q_p\cap\operatorname{row}Q_b)\ge h\}
          =\{\operatorname{rank}W\le u-h\}.
\]
For full-row-rank \(Q_p,Q_b\),
\[
\operatorname{codim}\mathcal I_h=h(n-b-u+h).
\]
Merely “meeting” does not force \(\|Q_p(I-\Pi_b)\|=0\) when \(u>1\); total vanishing requires \(\operatorname{row}Q_p\subseteq\operatorname{row}Q_b\).

[FACT] Set
\[
H=PU+BD,\qquad Y=\binom{P}{C}\in\mathbb R^{M_0\times u}.
\]
A determinant-one shear in the output columns turns
\[
PQ_p+BQ_b
\]
into \([H\mid PW]\), up to a bounded positive-definite metric. Consequently,
\[
F\asymp \|H\|_F^2+\|YW\|_F^2.
\]

[FACT] The exact Jacobian bookkeeping is
\[
dQ_b=|\det D|^{\,d}\,dD\,dX,\qquad
\det(Q_bQ_b^{\mathsf T})^{-a/2}
=|\det D|^{-a}\det(I+XX^{\mathsf T})^{-a/2},
\]
and
\[
dB=|\det D|^{-u}\,dH.
\]
Thus the joint determinant power is
\[
\boxed{|\det D|^{\,n-b-a-u}.}
\]

[FACT] On the rank-\(\ell\) chart of \(W\), its Schur normal block has size
\[
h\times(d-\ell),\qquad h=u-\ell.
\]
After smooth row and column operations,
\[
F\asymp |H|^2+|Y_1|^2+|Y_2E|^2.
\]
Stratifying by \(s=\operatorname{rank}Y_2\), the exact normal codimension is
\[
C_{\ell,s}
=ub+M_0\ell+(M_0-s)(u-\ell-s)+s(d-\ell).
\]
The associated radial chart is
\[
\boxed{\int_0^\delta r^{\,C_{\ell,s}-1-2q}\,dr.}
\]

[FACT] At a corank-\(k\) point of \(Q_b\), the Schur normal matrix is
\[
E_b\in\mathbb R^{k\times(n-b+k)}.
\]
If \(0<\tau_1\ll\cdots\ll\tau_k\) are its singular values, then
\[
dE_b\;\det(E_bE_b^{\mathsf T})^{-a/2}
\asymp
\prod_{i=1}^k
\tau_i^{\,n-b-a+2(i-1)}\,d\tau_i
\]
times angular units.

[FACT] In pivot-cancellation coordinates \(H_i=(PU)_i+\tau_iB_i\), the same chart is
\[
\prod_i
\tau_i^{\,n-b-a-u+2(i-1)}
\mathbf1_{\{|H_i-(PU)_i|\lesssim\tau_i\}}\,
d\tau_i\,dH_i.
\]
The shrinking tube indicator is part of the monomialisation; removing it changes the exponents.

[FACT] Therefore the Gram factor cannot be pulled out by a supremum:
\[
\sup_{Q_b}\det(Q_bQ_b^{\mathsf T})^{-a/2}=\infty.
\]
It must remain coupled to the pivot tube and transverse incidence variables.

[FACT] Moreover, its smallest-singular-value integral already requires
\[
n-b-a>-1
\iff
\boxed{a<n-b+1}.
\]
When equality holds, the Gram chart contains \(\int_0^\delta\tau^{-1}d\tau\).

[FACT] If \(n\ge M_1\), a stratum with \(\operatorname{corank}Q_b=k\) and incidence dimension \(h\) has \(k+h\) missing stacked-row directions. Hence an \(S_j\)-shell can contain both pure incidence strata and pure Gram-corank strata; the shell condition does not isolate incidence alone.

## Q3 — pointwise versus integrated domination

[FACT] A pointwise-in-\(z\) bound fails even in the intended \(s=0\)-binding regime. Take
\[
M=(3,3,5),\quad u=2,\quad a=b=1,\quad j=1.
\]
Here
\[
\minAdm(M)=9,\qquad T_1=\frac92.
\]
Choose
\[
Q_p(\delta)=
\begin{pmatrix}
1&0&0&0&0\\
0&\delta&0&0&0
\end{pmatrix},
\qquad Q_b=e_3.
\]

[FACT] For \(\delta<\varepsilon\), this lies in \(S_1\). The front loss is exactly
\[
F=|x|^2+\delta^2|y|^2,
\qquad x\in\mathbb R^5,\quad y\in\mathbb R^3.
\]
Consequently, for \(5/2<q<4\),
\[
\int F^{-q}\,dx\,dy\asymp\delta^{\,5-2q}.
\]

[FACT] Taking \(q=3\), hence \(c'=7/2<T_1\), gives growth \(\delta^{-1}\), while
\[
\|Q_p(\delta)\|_F^{-2q}=(1+\delta^2)^{-3}\asymp1.
\]
The same estimate holds on a fixed positive-measure neighborhood of \(Q_b=e_3\). Therefore the proposed pointwise ratio is unbounded.

[FACT] The rank-one stratum in \(2\times5\) matrices has codimension
\[
(2-1)(5-1)=4.
\]
Its normal radial integral is
\[
\int_0^\delta \rho^{\,4-1}\rho^{\,5-2q}\,d\rho
=
\int_0^\delta \rho^{\,8-2q}\,d\rho,
\]
which is finite for \(q<9/2\), in particular for \(q<4\).

[INFERENCE] Thus the condition-number blow-up can be integrable only after the \(z\)-integration participates. The shell does not remove it—the fixed \(Q_b\)-neighborhood remains inside \(S_1\); the rescuing factor is the codimension of the \(Q_p\) rank stratum.

[FACT] Nevertheless, the integrated inequality is not universally valid, as the following Gram-corank witness shows.

## Q4 — decisive counterexample

[FACT] Take
\[
\boxed{M=(3,3,3),\quad u=1,\quad a=b=2,\quad j=1,\quad c'=\frac52.}
\]
Then
\[
\minAdm(3,3,3)=\min(9,7,7,9)=7,\qquad
T_1=\frac72,
\]
and
\[
\frac{ab}{2}=2<\frac52<\frac72,\qquad q=c'-\frac{ab}{2}=\frac12.
\]

[FACT] Fix \(Q_p=e_3\). Near a rank-one \(Q_b\), use the chart
\[
Q_b=L
\begin{pmatrix}
1&v_1&v_2\\
0&x&y
\end{pmatrix},
\]
where \(L\) is uniformly invertible and all variables are small. Then
\[
\det(Q_bQ_b^{\mathsf T})
=\det(L)^2
\left((1+|v|^2)(x^2+y^2)-(v_1x+v_2y)^2\right)
\asymp x^2+y^2.
\]

[FACT] At \(x=y=0\), the stacked matrix \((Q_p;Q_b)\) has rank \(2\), with two singular values bounded below. For sufficiently small \(x,y\), the whole chart lies in \(S_1(Q_p)\).

[FACT] All matrices and projections are bounded on this chart, so the inner \(P,B,C\)-integral has a uniform positive lower bound. Therefore the \(A_{\rm cor}\)-integral dominates
\[
\int_{x^2+y^2<\delta^2}(x^2+y^2)^{-a/2}\,dx\,dy
=
\int_{x^2+y^2<\delta^2}(x^2+y^2)^{-1}\,dx\,dy
=
2\pi\int_0^\delta\frac{dr}{r}
=\infty.
\]

[FACT] This persists for an open neighborhood of \(Q_p=e_3\), so the outer \(z\)-integration does not remove the divergence.

[FACT] The reduced comparator has \(uM_2/2=3/2\) as its \(q\)-threshold, and \(q=1/2\). Its local radial integral is
\[
\int_0^\delta r^{\,3-1-2q}\,dr
=\int_0^\delta r\,dr<\infty.
\]

[FACT] Hence
\[
\boxed{\text{LHS}=\infty,\qquad \text{RHS}<\infty,}
\]
so no finite \(K_{j,c'}\) exists.

[FACT] **Final adjudication: FALSE as stated.**

[FACT] If “the binding case” was intended to impose the omitted hypothesis that \(s=0\) minimizes \(\minAdm\), then
\[
M_2\ge M_0+M_1-1,
\]
which forces \(a<M_2-b+1\) and excludes this Gram counterexample. Under that extra restriction the \(M=(2,2,3)\) corner is consistent with a true integrated estimate, but the pointwise-in-\(z\) domination still fails by the \(M=(3,3,5)\) example.