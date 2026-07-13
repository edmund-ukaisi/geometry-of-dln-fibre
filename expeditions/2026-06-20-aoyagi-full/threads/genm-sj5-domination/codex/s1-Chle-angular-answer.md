## (1) THRESHOLD

[FACT]  
\[
\sup\{c:J(c)<\infty\}=\frac{u\rho}{2},
\qquad J(c)<\infty\iff c<\frac{u\rho}{2}.
\]
Writing \(A=[P\ B_{12}]\in\mathbb R^{u\times M_1}\), the map \(A\mapsto AQ\) consists of \(u\) copies of \(x\mapsto xQ\); hence its rank is \(u\rho\). Its kernel has dimension \(u(M_1-\rho)\) and codimension \(u\rho\). Transversally, the integral is equivalent to
\[
\int_{\lVert z\rVert<\delta}\lVert z\rVert^{-2c}\,dz,\qquad z\in\mathbb R^{u\rho},
\]
which converges exactly when \(2c<u\rho\); equality gives logarithmic divergence. Thus the stated rank fact is correct, and the general sublevel exponent is \(u\rho/2\). The answer is independent of \(a,b,n\) except through \(\rho\).

## (2) NONCOMPACTNESS

[FACT] The \(|\det\widehat P|=1\) noncompactness and \(s^{-1}B_{12}\) amplification cause no additional divergence below \(u\rho/2\). The box imposes \(s\lVert\widehat P\rVert_\infty\le T\); writing \(\widetilde B=s^{-1}B_{12}\) gives \(dB_{12}=s^{ub}d\widetilde B\). These constraints and the \(P\)-blow-up Jacobian compensate the apparent angular tails.

[FACT] No: although
\[
\sigma_{\min}(\widehat P)\ge \sigma_{\max}(\widehat P)^{-(u-1)}
\]
is correct, its right-hand side tends to \(0\). It gives no uniform lower bound and ignores possible cancellation with \(B_{12}Q_b\). The integrand is unbounded for every \(c>0\), but integrable when \(c<u\rho/2\).

## (3) COMPARATOR

[FACT] The exact threshold condition is
\[
\boxed{\minAdm(u,M_2,\ldots,M_{\mathrm{last}})
\le u\rho
=u\min(M_1,\ldots,M_{\mathrm{last}}).}
\]

[FACT] For \(M=(3,3,3)\), \(u=2\): \(\rho=3\), so \(J\)-threshold \(=3\); \(M'=(2,3)\), \(\minAdm(M')=6\), so comparator threshold \(=3\). They are equally singular.

[FACT] For \(M=(3,3,4,4)\), \(u=2\): \(J\)-threshold \(=3\), while
\[
\minAdm(2,4,4)=\min(8,\,3+4,\,8)=7,
\]
so comparator threshold \(=7/2\). Here \(J\) is more singular.

## (4) VERDICT

[FACT] **(b)** A finite absorption constant throughout the comparator’s convergence range is possible only under \(\minAdm(M')\le u\rho\); [INFERENCE] threshold comparison alone does not establish a constant uniform in \(c\) at criticality.