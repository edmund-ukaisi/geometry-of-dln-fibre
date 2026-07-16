For any fixed \(S\) of rank \(\rho\),

\[
\boxed{\operatorname{Ch}(S)<\infty \iff a<\rho-b+1}
\]

equivalently,

\[
\boxed{\rho>a+b-1}.
\]

Since the parameters are integers, this is \(\rho\ge a+b\).

Let \(X=AS\), expressed in the \(\rho\)-dimensional image of \(S\). The singular locus

\[
\Sigma=\{X\in\mathbb R^{b\times \rho}:\operatorname{rank}X<b\}
\]

has codimension

\[
d=\rho-b+1.
\]

At a smooth rank-\((b-1)\) point, write \(z\in\mathbb R^d\) for the normal coordinates. Gram–Schmidt gives

\[
\det(XX^{T})\asymp |z|^2.
\]

Thus the integrand is locally \(|z|^{-a}\), and

\[
\int_0^\varepsilon r^{d-1-a}\,dr
\]

converges exactly when \(a<d\). At \(a=d\), it is \(\int_0^\varepsilon dr/r\): logarithmic divergence.

Lower-rank strata impose no stronger condition. Indeed, for rows \(x_1,\dots,x_b\),

\[
\det(XX^T)
=\prod_{j=1}^b
\operatorname{dist}\!\left(x_j,\operatorname{span}(x_1,\dots,x_{j-1})\right)^2.
\]

At stage \(j\), the transverse dimension is \(\rho-j+1\); the strongest condition occurs at \(j=b\).

Therefore, at

\[
\rho=a+b-1,
\]

the charge diverges logarithmically.

For \(b=2,a=2,\rho=3,S=I_3\), the transverse dimension is \(2\), while the integrand behaves as \(|z|^{-2}\) in \(\mathbb R^2\). Hence

\[
\int_{[-1,1]^{2\times3}}\det(AA^T)^{-1}\,dA=+\infty
\]

with logarithmic divergence.

The \(b(n-\rho)\) directions annihilated by \(S\) do not change the threshold: over a bounded box they contribute only a finite, locally positive fiber-volume factor. Over an unbounded domain they would instead cause a separate infinite-volume divergence.

For Question 2, at the boundary,

\[
\boxed{I=+\infty}.
\]

For almost every \(S\) in the \(S\)-box, \(\operatorname{rank}S=\rho\), and Tonelli gives

\[
\int_{A,\Delta} f_S(A)g_S(\Delta)\,dA\,d\Delta
=
\left(\int_A f_S(A)\,dA\right)
\left(\int_\Delta g_S(\Delta)\,d\Delta\right).
\]

The first factor is \(+\infty\); by the stated assumption the second is finite and strictly positive. Hence the inner integral is \(+\infty\) for almost every generic \(S\), so its \(S\)-integral is \(+\infty\).

Thus neither varying \(S\) nor the loss factor can regularize the divergence. The decisive mechanism is nonnegative Tonelli factorization conditional on \(S\); correlation through \(S\) cannot produce cancellation.

All claims above are exact Lebesgue-integrability arguments. The only structural assumption is that the boxes are nondegenerate and the \(A\)-box meets the rank-deficient locus, as the centered boxes in the question do.