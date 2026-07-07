1. **Q1: atom-artifact.**

For the caricature
\[
F=\alpha^2+\gamma^2\beta^2s^2,
\]
the exact RLCT is
\[
\lambda=1
\]
with pole multiplicity \(3\).

Toric computation: the exponent vectors are
\[
(2,0,0,0),\qquad (0,2,2,2).
\]
For weights \(w\),
\[
d(w)=\min(2w_\alpha,2w_\gamma+2w_\beta+2w_s),
\]
so normalizing \(d(w)=1\) gives
\[
w_\alpha\ge \tfrac12,\qquad w_\gamma+w_\beta+w_s\ge \tfrac12.
\]
The minimum of \(w_\alpha+w_\gamma+w_\beta+w_s\) is \(1\). Thus \(F^{-c}\) is locally integrable iff \(c<1\). This is the standard Newton/toric monomial computation for such nondegenerate sums of monomials. ([arxiv.org](https://arxiv.org/abs/math/0003232?utm_source=openai))

The atom route’s formula
\[
\int d\gamma\,(\alpha^2+\gamma^2(\beta s)^2)^{-c}
\sim |\beta s|^{-1}\alpha^{1-2c}
\]
is only the large-parameter asymptotic when \(|\beta s|\gg |\alpha|\). It is not uniform near \(\beta s=0\). The exact inner integral has a crossover:
\[
\int d\gamma\,(\alpha^2+\gamma^2t^2)^{-c}
\lesssim |\alpha|^{-2c}\min\{1,|\alpha|/|t|\},
\qquad t=\beta s.
\]
After integrating \(\alpha\), this gives roughly
\[
|t|^{1-2c}=|\beta s|^{1-2c},
\]
not \(|\beta s|^{-1}\). Then
\[
\int |\beta s|^{1-2c}\,d\beta\,ds<\infty
\quad\Longleftrightarrow\quad c<1.
\]

So the \(|\beta s|^{-1}\) wall is not the true wall. It is an artifact of integrating out \(\gamma\) at fixed degenerating downstream scale and then using a non-uniform asymptotic as though it were an equality.

2. **Q2: yes, full blowup avoids the coupling.**

If the blowup route genuinely reaches normal crossings, then on each chart
\[
F=(\text{monomial})^2\cdot U,
\qquad U\ge c_0>0,
\]
and the Jacobian is also monomial times a unit. The local integral becomes
\[
\int \prod_i |y_i|^{\kappa_i-2cN_i}\cdot U(y)^{-c}\,dy,
\]
so finiteness is exactly the coordinatewise endpoint condition
\[
\kappa_i-2cN_i>-1
\]
on every chart.

There is then no surviving Gram determinant and no downstream coupling. Any determinant-type factor has either become a monomial factor accounted for in the exponents, or a unit on that chart. The product structure does not obstruct normal crossing in principle: the entries of the matrix product generate an algebraic ideal, and log-principalization/resolution of ideals in characteristic zero exists. ([arxiv.org](https://arxiv.org/abs/math/0702836?utm_source=openai))

Caveat: one must still prove that the specific proposed layer-by-layer radial blowups actually give that normal-crossing form. But once they do, the coupling is gone by definition.

3. **Q3: correct routes compute the same threshold; the displayed atom route is mishandling a non-uniform limit.**

A correct atom route and a correct full-resolution route must compute the same RLCT, because the RLCT is intrinsic.

If ROUTE-ATOM walls while ROUTE-BLOWUP is finite for the same \(c'<\mathrm{RLCT}(F)\), the atom route has not computed the original integral. It has replaced the exact inner integral by a full-rank/asymptotic Gaussian formula whose constant blows up at downstream rank drop, and it has ignored the scale relation between the core variable and the downstream degeneracy.

In the caricature, the lost information is precisely the cutoff
\[
|\alpha|\lessgtr |\beta s|.
\]
That cutoff changes the apparent \(|\beta s|^{-1}\) into the integrable exponent \(|\beta s|^{1-2c}\) for \(c<1\). Thus the “wall” is genuine for the incorrectly reduced outer integrand, but artificial for the original joint integral.