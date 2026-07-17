## Q1

**PROVEN, with a core-convention caveat.** A uniformly positive core produces no blow-up. The inverse-Gram weight appears only for \(w\downarrow0\).

Let \(Q=CZ\), \(s=\operatorname{rank}Q\), and let \(\sigma_1,\dots,\sigma_s>0\) be its nonzero singular values. After an orthogonal change of \(\Delta\)-coordinates,

\[
\|\Delta Q\|_F^2
=
\sum_{\alpha=1}^r\sum_{j=1}^s \sigma_j^2x_{\alpha j}^2.
\]

Thus the exact residual finite-box integral is

\[
I_c(w,Q)=
\int_{D'}
\left(
w+\sum_{\alpha,j}\sigma_j^2x_{\alpha j}^2
\right)^{-c}\,dX\,dY,
\]

where \(Y\) parametrizes the \(r(k-s)\)-dimensional kernel.

For the transverse whole-space integral, when \(c>rs/2\),

\[
\int_{\mathbb R^{rs}}
\left(
w+\sum_{\alpha,j}\sigma_j^2x_{\alpha j}^2
\right)^{-c}dX
=
\pi^{rs/2}
\frac{\Gamma(c-rs/2)}{\Gamma(c)}
w^{rs/2-c}
\prod_{j=1}^s\sigma_j^{-r}.
\]

Equivalently,

\[
\prod_{j=1}^s\sigma_j^{-r}
=
\operatorname{pdet}(QQ^T)^{-r/2}.
\]

On the generic full-row-rank stratum \(s=k\),

\[
I_c(w,Q)\sim
K\,
w^{rk/2-c}
\det(QQ^T)^{-r/2}.
\]

Hence this inverse-Gram weight blows up along

\[
\boxed{\operatorname{rank}(CZ)<k}
\]

provided \(CZ\) can generically have rank \(k\). If its generic rank is only \(s_{\max}<k\), replace \(k\) by \(s_{\max}\).

At \(w=0\), transverse integrability is exact:

\[
I_c(0,Q)<\infty
\quad\Longleftrightarrow\quad
c<\frac{r\,\operatorname{rank}(CZ)}2.
\]

Thus for fixed \(c\), the actual infinite locus is

\[
\boxed{\left\{(C,Z):\,2c\ge r\,\operatorname{rank}(CZ)\right\}}.
\]

If instead \(w\ge w_0>0\), then

\[
I_c(w,Q)\le \operatorname{vol}(D)\,w_0^{-c},
\]

so there is no rank blow-up at all.

For \(k\le q\), Cauchy–Binet gives

\[
\det(QQ^T)=
\sum_{\substack{J\subseteq\{1,\dots,q\}\\ |J|=k}}
\det(Q_{[:,J]})^2,
\]

and

\[
\det((CZ)_{I,J})
=
\sum_{|S|=|I|}
\det(C_{I,S})\det(Z_{S,J}).
\]

Hence \(\operatorname{rank}(CZ)\le\rho\) is exactly the vanishing of all \((\rho+1)\)-minors. In free \(Q\)-space this determinantal locus has codimension

\[
(k-\rho)(q-\rho),
\]

but its preimage in \((C,Z)\)-space need not have that codimension.

## Q2

**PROVEN.** For \(r=1\), the intermediate matrix \(\Delta C\) has rank only \(0\) or \(1\).

Write

\[
\Delta=(\delta_1,\dots,\delta_k),\qquad
C=(c_{ij}),\qquad
Z=(z_{j\ell}),
\]

and set

\[
\gamma=\Delta C,\qquad
\gamma_j=\sum_{i=1}^k\delta_i c_{ij}.
\]

Then

\[
(\Delta CZ)_\ell
=
\sum_{j=1}^{M_2}\gamma_jz_{j\ell}
=
\sum_{i=1}^k\sum_{j=1}^{M_2}
\delta_i c_{ij}z_{j\ell},
\]

so

\[
\boxed{
\|\Delta CZ\|_F^2
=
\sum_{\ell=1}^q
\left(
\sum_{i,j}\delta_i c_{ij}z_{j\ell}
\right)^2
=
\gamma ZZ^T\gamma^T
=
\Delta CZZ^TC^T\Delta^T.
}
\]

Moreover,

\[
\operatorname{rank}(\Delta C)
=
\begin{cases}
0,&\Delta C=0,\\
1,&\Delta C\ne0.
\end{cases}
\]

In general,

\[
\operatorname{rank}(\Delta C)
\le
\min(\operatorname{rank}\Delta,\operatorname{rank}C)
\le \min(r,k,M_2),
\]

with generic rank \(\min(r,k,M_2)\).

For \(r=1\),

\[
\operatorname{rank}((\Delta C)Z)\le1.
\]

Therefore only \(\rho=0\) is a nontrivial rank-drop condition:

\[
\{(\Delta C)Z=0\}
=
\{\gamma=0\}
\cup
\{\,\gamma\ne0,\ \operatorname{im}Z\subseteq\ker\gamma\,\}.
\]

This remains a bilinear incidence variety, but it is a rank-one one; it is not a product of two factors both capable of rank at least \(2\).

Dimension correction: \((\Delta C)Z\) is \(r\times q\), hence \(1\times q\) here—not \(k\times q\).

## Q3

**PROVEN for the algebraic rank boundary; resolution “necessity” requires a precise definition of allowed centers.**

Let \(P=\Delta C\). Its generic rank is

\[
\operatorname{rank}_{\mathrm{gen}}P=\min(r,k,M_2).
\]

If the deep product \(Z\) has generic rank \(s_Z\), then both factors \(P\) and \(Z\) can have rank at least \(2\) exactly when

\[
\min(r,k,M_2)\ge2
\quad\text{and}\quad
s_Z\ge2.
\]

Under the intended non-bottleneck assumption \(M_2,s_Z\ge2\), the requested boundary is

\[
\boxed{\text{rank-one/single-factor regime iff }\min(r,k)\le1.}
\]

Thus the blank is \(\boxed{1}\).

Indeed, when \(\operatorname{rank}P\le1\), locally \(P=uv^T\), and

\[
\|PZ\|_F^2
=
\|u(v^TZ)\|_F^2
=
\|u\|^2\,\|v^TZ\|^2,
\]

the advertised rank-one free-bilinear leaf.

When \(\min(r,k)\ge2\) and downstream dimensions permit rank \(2\), the multiplication map

\[
\mu(P,Z)=PZ
\]

contains the genuine rank-\(\ge2\) matrix-product problem. Its differential satisfies

\[
d\mu_{(P,Z)}(X,Y)=XZ+PY,
\]

with

\[
\operatorname{coker}d\mu_{(P,Z)}
\simeq
\operatorname{Hom}(\ker Z,\operatorname{coker}P).
\]

When both kernel and cokernel are nonzero, rank strata of the two individual factors are not transverse; joint alignment data survive.

Two caveats:

1. Without downstream assumptions, the exact collapse condition is governed by \(\min(r,k,M_2,s_Z)\), not merely \(\min(r,k)\).
2. If “resolution” refers to the Q1 residual after integrating \(\Delta\) first, the boundary is not controlled by \(r\): even for \(r=1,k=2\), the residual blows up on \(\operatorname{rank}(CZ)<2\).

## Q4

**PROVEN under the natural convention that \(B\) is also integrated.**

The integral is

\[
I_c(\varepsilon)=
\int_{\Box_\varepsilon}
\left(
\|BZ\|_F^2+\|\Delta CZ\|_F^2
\right)^{-c}
\,dB\,d\Delta\,dC\,dZ.
\]

Set \(\gamma=\Delta C\) and

\[
A=
\begin{pmatrix}
B\\ \gamma
\end{pmatrix}.
\]

Then

\[
\|BZ\|^2+\|\Delta CZ\|^2=\|AZ\|_F^2.
\]

The pushforward of \(d\Delta\,dC\) under \((\Delta,C)\mapsto\gamma\) has only a logarithmic singularity. Writing \(\Delta=\rho u\) and decomposing both columns of \(C\) parallel/perpendicular to \(u\),

\[
d\Delta\,dC
\leadsto
\rho\,d\rho\cdot\rho^{-2}d\gamma,
\]

so its density satisfies

\[
h(\gamma)\lesssim 1+\log\frac{1}{\|\gamma\|}.
\]

In particular \(h\in L^p_{\mathrm{loc}}\) for every finite \(p\), so it does not change the strict threshold of the free \(2\times2\) product \(AZ\).

Near a rank-one/rank-one zero of \(AZ\), analytic invertible changes give

\[
A\sim
\begin{pmatrix}1&0\\0&a\end{pmatrix},
\qquad
Z'=
\begin{pmatrix}x_1&x_2\\y_1&y_2\end{pmatrix},
\]

and

\[
\|AZ\|_F^2\asymp
x_1^2+x_2^2+a^2(y_1^2+y_2^2).
\]

If \(y\ne0\), this is a nondegenerate quadratic form in the three normal variables \((x_1,x_2,a)\). Therefore

\[
\int_{\mathbb R^3}|u|^{-2c}du<\infty
\quad\Longleftrightarrow\quad c<\frac32.
\]

The \(y=0\) corner gives the same bound: after integrating \(x\), the remaining power is

\[
|a|^{2-2c}\|y\|^{2-2c},
\]

whose restrictive condition is again \(c<3/2\). Consequently

\[
\boxed{c_*=\frac32}.
\]

The charge comparison is

\[
\minAdm(1,2,2)=2,\qquad
\minAdm(2,2,2)=3,
\]

and

\[
\minAdm(2,3,2,2)
=
\min\{6,\ 2+2,\ 0+3\}=3.
\]

Hence

\[
\boxed{2c_*=3=\minAdm(2,3,2,2)},
\]

whereas the specified \(t=1\) peel ledger gives

\[
(M_0-t)(M_1-t)+\minAdm(1,2,2)
=1\cdot2+2=4.
\]

Thus the integral as written does not isolate the \(t=1\) charged contribution: it lacks the source-rank-drop Jacobian/radial weight responsible for the extra charge. It instead sees the global numerator \(3\).

On “single-factor”: the threshold admits an elementary rank-stratification/free-bilinear proof. But strictly, blow-ups only of the individual factor-rank loci do not principalize the full Q4 ideal. At the balanced point above, the local ideal is

\[
(x_1,x_2,a),
\]

a joint codimension-\(3\) center, while the two individual rank-one loci are Cartier determinant divisors. The \(BZ\) core has stacked a second row onto \(\Delta C\), restoring an effective generic \(2\times2\) product.

Finally, if \(B\) was meant as a fixed parameter rather than integrated:

\[
c_*=
\begin{cases}
3/2,&B\ne0,\\
1,&B=0.
\end{cases}
\]

If \(w\) is genuinely bounded below by a positive constant, then every \(c\) is integrable. Also, \(w=\|BZ\|^2\) is not positive on the full angular sphere: nonzero pairs with \(BZ=0\) exist.
tokens used
78,310
Conventions: “free” means integrated over a box containing the origin. Threshold means finiteness for \(c<c_*\) and divergence for \(c\ge c_*\).

## Q1

**PROVEN, with a core-convention caveat.** A uniformly positive core produces no blow-up. The inverse-Gram weight appears only for \(w\downarrow0\).

Let \(Q=CZ\), \(s=\operatorname{rank}Q\), and let \(\sigma_1,\dots,\sigma_s>0\) be its nonzero singular values. After an orthogonal change of \(\Delta\)-coordinates,

\[
\|\Delta Q\|_F^2
=
\sum_{\alpha=1}^r\sum_{j=1}^s \sigma_j^2x_{\alpha j}^2.
\]

Thus the exact residual finite-box integral is

\[
I_c(w,Q)=
\int_{D'}
\left(
w+\sum_{\alpha,j}\sigma_j^2x_{\alpha j}^2
\right)^{-c}\,dX\,dY,
\]

where \(Y\) parametrizes the \(r(k-s)\)-dimensional kernel.

For the transverse whole-space integral, when \(c>rs/2\),

\[
\int_{\mathbb R^{rs}}
\left(
w+\sum_{\alpha,j}\sigma_j^2x_{\alpha j}^2
\right)^{-c}dX
=
\pi^{rs/2}
\frac{\Gamma(c-rs/2)}{\Gamma(c)}
w^{rs/2-c}
\prod_{j=1}^s\sigma_j^{-r}.
\]

Equivalently,

\[
\prod_{j=1}^s\sigma_j^{-r}
=
\operatorname{pdet}(QQ^T)^{-r/2}.
\]

On the generic full-row-rank stratum \(s=k\),

\[
I_c(w,Q)\sim
K\,
w^{rk/2-c}
\det(QQ^T)^{-r/2}.
\]

Hence this inverse-Gram weight blows up along

\[
\boxed{\operatorname{rank}(CZ)<k}
\]

provided \(CZ\) can generically have rank \(k\). If its generic rank is only \(s_{\max}<k\), replace \(k\) by \(s_{\max}\).

At \(w=0\), transverse integrability is exact:

\[
I_c(0,Q)<\infty
\quad\Longleftrightarrow\quad
c<\frac{r\,\operatorname{rank}(CZ)}2.
\]

Thus for fixed \(c\), the actual infinite locus is

\[
\boxed{\left\{(C,Z):\,2c\ge r\,\operatorname{rank}(CZ)\right\}}.
\]

If instead \(w\ge w_0>0\), then

\[
I_c(w,Q)\le \operatorname{vol}(D)\,w_0^{-c},
\]

so there is no rank blow-up at all.

For \(k\le q\), Cauchy–Binet gives

\[
\det(QQ^T)=
\sum_{\substack{J\subseteq\{1,\dots,q\}\\ |J|=k}}
\det(Q_{[:,J]})^2,
\]

and

\[
\det((CZ)_{I,J})
=
\sum_{|S|=|I|}
\det(C_{I,S})\det(Z_{S,J}).
\]

Hence \(\operatorname{rank}(CZ)\le\rho\) is exactly the vanishing of all \((\rho+1)\)-minors. In free \(Q\)-space this determinantal locus has codimension

\[
(k-\rho)(q-\rho),
\]

but its preimage in \((C,Z)\)-space need not have that codimension.

## Q2

**PROVEN.** For \(r=1\), the intermediate matrix \(\Delta C\) has rank only \(0\) or \(1\).

Write

\[
\Delta=(\delta_1,\dots,\delta_k),\qquad
C=(c_{ij}),\qquad
Z=(z_{j\ell}),
\]

and set

\[
\gamma=\Delta C,\qquad
\gamma_j=\sum_{i=1}^k\delta_i c_{ij}.
\]

Then

\[
(\Delta CZ)_\ell
=
\sum_{j=1}^{M_2}\gamma_jz_{j\ell}
=
\sum_{i=1}^k\sum_{j=1}^{M_2}
\delta_i c_{ij}z_{j\ell},
\]

so

\[
\boxed{
\|\Delta CZ\|_F^2
=
\sum_{\ell=1}^q
\left(
\sum_{i,j}\delta_i c_{ij}z_{j\ell}
\right)^2
=
\gamma ZZ^T\gamma^T
=
\Delta CZZ^TC^T\Delta^T.
}
\]

Moreover,

\[
\operatorname{rank}(\Delta C)
=
\begin{cases}
0,&\Delta C=0,\\
1,&\Delta C\ne0.
\end{cases}
\]

In general,

\[
\operatorname{rank}(\Delta C)
\le
\min(\operatorname{rank}\Delta,\operatorname{rank}C)
\le \min(r,k,M_2),
\]

with generic rank \(\min(r,k,M_2)\).

For \(r=1\),

\[
\operatorname{rank}((\Delta C)Z)\le1.
\]

Therefore only \(\rho=0\) is a nontrivial rank-drop condition:

\[
\{(\Delta C)Z=0\}
=
\{\gamma=0\}
\cup
\{\,\gamma\ne0,\ \operatorname{im}Z\subseteq\ker\gamma\,\}.
\]

This remains a bilinear incidence variety, but it is a rank-one one; it is not a product of two factors both capable of rank at least \(2\).

Dimension correction: \((\Delta C)Z\) is \(r\times q\), hence \(1\times q\) here—not \(k\times q\).

## Q3

**PROVEN for the algebraic rank boundary; resolution “necessity” requires a precise definition of allowed centers.**

Let \(P=\Delta C\). Its generic rank is

\[
\operatorname{rank}_{\mathrm{gen}}P=\min(r,k,M_2).
\]

If the deep product \(Z\) has generic rank \(s_Z\), then both factors \(P\) and \(Z\) can have rank at least \(2\) exactly when

\[
\min(r,k,M_2)\ge2
\quad\text{and}\quad
s_Z\ge2.
\]

Under the intended non-bottleneck assumption \(M_2,s_Z\ge2\), the requested boundary is

\[
\boxed{\text{rank-one/single-factor regime iff }\min(r,k)\le1.}
\]

Thus the blank is \(\boxed{1}\).

Indeed, when \(\operatorname{rank}P\le1\), locally \(P=uv^T\), and

\[
\|PZ\|_F^2
=
\|u(v^TZ)\|_F^2
=
\|u\|^2\,\|v^TZ\|^2,
\]

the advertised rank-one free-bilinear leaf.

When \(\min(r,k)\ge2\) and downstream dimensions permit rank \(2\), the multiplication map

\[
\mu(P,Z)=PZ
\]

contains the genuine rank-\(\ge2\) matrix-product problem. Its differential satisfies

\[
d\mu_{(P,Z)}(X,Y)=XZ+PY,
\]

with

\[
\operatorname{coker}d\mu_{(P,Z)}
\simeq
\operatorname{Hom}(\ker Z,\operatorname{coker}P).
\]

When both kernel and cokernel are nonzero, rank strata of the two individual factors are not transverse; joint alignment data survive.

Two caveats:

1. Without downstream assumptions, the exact collapse condition is governed by \(\min(r,k,M_2,s_Z)\), not merely \(\min(r,k)\).
2. If “resolution” refers to the Q1 residual after integrating \(\Delta\) first, the boundary is not controlled by \(r\): even for \(r=1,k=2\), the residual blows up on \(\operatorname{rank}(CZ)<2\).

## Q4

**PROVEN under the natural convention that \(B\) is also integrated.**

The integral is

\[
I_c(\varepsilon)=
\int_{\Box_\varepsilon}
\left(
\|BZ\|_F^2+\|\Delta CZ\|_F^2
\right)^{-c}
\,dB\,d\Delta\,dC\,dZ.
\]

Set \(\gamma=\Delta C\) and

\[
A=
\begin{pmatrix}
B\\ \gamma
\end{pmatrix}.
\]

Then

\[
\|BZ\|^2+\|\Delta CZ\|^2=\|AZ\|_F^2.
\]

The pushforward of \(d\Delta\,dC\) under \((\Delta,C)\mapsto\gamma\) has only a logarithmic singularity. Writing \(\Delta=\rho u\) and decomposing both columns of \(C\) parallel/perpendicular to \(u\),

\[
d\Delta\,dC
\leadsto
\rho\,d\rho\cdot\rho^{-2}d\gamma,
\]

so its density satisfies

\[
h(\gamma)\lesssim 1+\log\frac{1}{\|\gamma\|}.
\]

In particular \(h\in L^p_{\mathrm{loc}}\) for every finite \(p\), so it does not change the strict threshold of the free \(2\times2\) product \(AZ\).

Near a rank-one/rank-one zero of \(AZ\), analytic invertible changes give

\[
A\sim
\begin{pmatrix}1&0\\0&a\end{pmatrix},
\qquad
Z'=
\begin{pmatrix}x_1&x_2\\y_1&y_2\end{pmatrix},
\]

and

\[
\|AZ\|_F^2\asymp
x_1^2+x_2^2+a^2(y_1^2+y_2^2).
\]

If \(y\ne0\), this is a nondegenerate quadratic form in the three normal variables \((x_1,x_2,a)\). Therefore

\[
\int_{\mathbb R^3}|u|^{-2c}du<\infty
\quad\Longleftrightarrow\quad c<\frac32.
\]

The \(y=0\) corner gives the same bound: after integrating \(x\), the remaining power is

\[
|a|^{2-2c}\|y\|^{2-2c},
\]

whose restrictive condition is again \(c<3/2\). Consequently

\[
\boxed{c_*=\frac32}.
\]

The charge comparison is

\[
\minAdm(1,2,2)=2,\qquad
\minAdm(2,2,2)=3,
\]

and

\[
\minAdm(2,3,2,2)
=
\min\{6,\ 2+2,\ 0+3\}=3.
\]

Hence

\[
\boxed{2c_*=3=\minAdm(2,3,2,2)},
\]

whereas the specified \(t=1\) peel ledger gives

\[
(M_0-t)(M_1-t)+\minAdm(1,2,2)
=1\cdot2+2=4.
\]

Thus the integral as written does not isolate the \(t=1\) charged contribution: it lacks the source-rank-drop Jacobian/radial weight responsible for the extra charge. It instead sees the global numerator \(3\).

On “single-factor”: the threshold admits an elementary rank-stratification/free-bilinear proof. But strictly, blow-ups only of the individual factor-rank loci do not principalize the full Q4 ideal. At the balanced point above, the local ideal is

\[
(x_1,x_2,a),
\]

a joint codimension-\(3\) center, while the two individual rank-one loci are Cartier determinant divisors. The \(BZ\) core has stacked a second row onto \(\Delta C\), restoring an effective generic \(2\times2\) product.

Finally, if \(B\) was meant as a fixed parameter rather than integrated:

\[
c_*=
\begin{cases}
3/2,&B\ne0,\\
1,&B=0.
\end{cases}
\]

If \(w\) is genuinely bounded below by a positive constant, then every \(c\) is integrable. Also, \(w=\|BZ\|^2\) is not positive on the full angular sphere: nonzero pairs with \(BZ=0\) exist.
