### Q1. Pushforward density

Up to normalization,
\[
\rho(Y)=\int_{\substack{P\in[-1,1]^{2\times2}\\P^{-1}Y\in[-1,1]^{2\times2}}}
|\det P|^{-2}\,dP .
\]
Writing \(a=\sigma_{\max}(Y)\), \(b=\sigma_{\min}(Y)\), the classical local estimate is
\[
\rho(Y)\asymp \frac{1+\log(a/b)}{a}
\]
on interior angular sectors.

Thus the singularity is stratified:

- Near a nonzero rank-one matrix (\(a\asymp1,\ b\to0\)): \(\rho(Y)\asymp\log(1/b)\). Hence generic power order \(A=0\).
- Along balanced approaches to \(Y=0\) (\(a\asymp b\asymp r\)): \(\rho(Y)\asymp r^{-1}\). Hence the worst uniform power order is \(A=1\).

So it is not simply a power along the whole determinant hypersurface.

### Q2. Does B alone suffice?

**Yes. The exact threshold \(c'<3/2\) is reachable; there is no gap.**

Let \(E_r=\{r/2<\sigma_{\max}(Y)\le r\}\), with dyadic \(r\). Put \(Y=rX\). On \(E_r\),
\[
\rho(rX)\lesssim r^{-1}L(X),\qquad
L(X)=1+|\log\sigma_{\min}(X)|.
\]
Here \(L\in L^p\) for every finite \(p\), since \(X\) remains away from zero and the remaining singularity is logarithmic.

Choose \(q>1\) with \(c'q<3/2\), and let \(p=q/(q-1)\). Hölder—or pointwise Young followed by Tonelli—and B at exponent \(c'q\) give
\[
\int L(X)\|XW\|^{-2c'}\,dX\,dW<\infty .
\]
The \(r\)-shell therefore contributes at most
\[
C\,r^{4}\,r^{-1}\,r^{-2c'}=C r^{3-2c'}.
\]
Summing dyadic shells converges exactly when \(c'<3/2\). This is a proof, not merely an inference.

### Q3. Fixed-box decoupling and crude folding

The decoupling integral
\[
\int_{[-1,1]^{2\times2}}|\det P|^{-2}\,dP
\]
diverges: near a smooth point of \(\{\det P=0\}\), determinant is a normal coordinate \(t\), giving \(\int |t|^{-2}dt=\infty\). Hence that enlarged-domain bound is vacuous.

On the balanced \(Y\to0\) sector with \(W\) uniformly nonsingular, \(\rho(Y)\asymp\|YW\|^{-1}\), so \(A=1\). Folding this pointwise into B requires
\[
c''=c'+\tfrac12<\tfrac32,
\]
and reaches only \(c'<1\): an apparent loss of \(1/2\). It does not match the true threshold and is weaker than the shell argument above.

### Q4. Scalar model

Uniform Gaussian asymptotics give
\[
\int_{[-1,1]^2}e^{-N(1+c^2)z^2}\,dz\,dc
\sim
2\sqrt{\pi}\,\operatorname{arsinh}(1)\,N^{-1/2}.
\]
There is no logarithm. Extracting a non-integrable \(|z|^{-1}\) weight destroys the coupling and incorrectly predicts worse decay; that reduction is unsound.

### Q5. General criterion

Suppose \(f\asymp d^m\) near the relevant locus and \(\rho\lesssim d^{-A}\). Direct absorption into an unweighted bound with threshold \(c_*\) requires
\[
c'+\frac{A}{m}<c_*,
\qquad\text{equivalently}\qquad
A<m(c_*-c').
\]

Alternatively, for a codimension-\(k\) locus, Hölder works precisely when
\[
A<k\,\frac{c_*-c'}{c_*}.
\]
If neither inequality holds and no homogeneous shell factorization supplies separate summability, an unweighted black box cannot control the weight; pinned charts or a weighted/coupled induction hypothesis are then required.