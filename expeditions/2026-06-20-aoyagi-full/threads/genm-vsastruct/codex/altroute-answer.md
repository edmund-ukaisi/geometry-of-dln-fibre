## Q1

Yes. Route 2 avoids both the factor \(|\det M|^{-4}\) and the associated sector \(\{|\det M|\ge\eta\}\). It still needs outer good-chart/rank sectors, but not the casting sector.

**FACT.** For fixed \(\theta=(P,C,W,A_2)\), write
\[
L_\theta(\Gamma,v)=\bigl(PvA_2,\,(Cv+\Gamma W)A_2\bigr).
\]
If \(L_\theta(\Gamma,v)=0\), the right inverse of \(A_2\) and left inverse of \(P\) give \(v=0\); then the right inverse of \(W\) gives \(\Gamma=0\). Hence
\[
g_{\rm cc}(\Gamma,v)=\|L_\theta(\Gamma,v)\|^2
\]
is a positive-definite quadratic form on
\[
\mathbb R^{ab+th}=\mathbb R^{4+3}=\mathbb R^7.
\]
Consequently its cube integral is finite exactly for
\[
c'<\frac72,
\]
and diverges logarithmically at \(c'=7/2\).

**FACT.**
\[
\frac72=\frac12\minAdm(3,3,3,4),
\qquad \minAdm(3,3,3,4)=7.
\]

It is also exactly Route 1’s value:
\[
\frac{h_0+h_1+2}{2}
=\frac{3+2+2}{2}
=\frac72.
\]
Here \(h_0+1=4=\dim\Gamma\) and \(h_1+1=3=\dim v\). Thus the isotropic \(7\)-corner and the weighted \(4+3\) corner have the same codimension-addition mechanism and critical exponent, though they are not literally the same normal-form integral.

**INFERENCE.** The native presentation is stronger conceptually: it obtains the \(7/2\) directly from the actual seven-dimensional quadratic loss, without manufacturing two radial units and then recombining their codimensions.

## Q2

The determinant inverse is genuinely eliminated, not relocated.

**FACT.** Define the sphere minimum
\[
a(\theta)=\min_{\|x\|=1}\|L_\theta x\|^2
         =\sigma_{\min}(L_\theta)^2.
\]
On a good chart, \(a(\theta)>0\), and
\[
g_{\rm cc}(x)\ge a(\theta)\|x\|^2.
\]
Therefore
\[
\int_{\text{cube}}g_{\rm cc}(x)^{-c'}\,dx
\le C_{c'}\,a(\theta)^{-c'}
=C_{c'}\,\sigma_{\min}(L_\theta)^{-2c'}.
\]
This is a coercivity/smallest-singular-value weight, not a change-of-variables Jacobian.

The distinction is substantive. For example, \(W=(e_1;e_2)\) and \(\bar v=e_1\) give \(\det[w_1;w_2;\bar v]=0\), while the native quadratic form remains positive definite whenever \(P,W,A_2\) satisfy the good-chart hypotheses. Thus the casting determinant can vanish where the native slice has no degeneration at all.

**FACT.** Outer nonuniformity occurs when the actual injectivity data \(P,W,A_2\) approach rank loss. That is intrinsic to the original loss. The casting factor \(|\det M|^{-4}\), by contrast, comes solely from reparametrizing \(A_2\).

**INFERENCE.** The deeper proof may use rank strata, several singular values, or determinant/minor estimates as tools. That would not resurrect or relocate the casting determinant. Also, the crude bound \(a^{-c'}\) may be too coarse globally; proving its integrability—or replacing it with a sharper anisotropic estimate—is precisely part of the deeper \((S,J)\) rung.

## Q3

The native route is the cleaner primitive.

**FACT.** Under the stated bank:

- Route 2’s inner work is already covered by chart equality, \(v\)-exposure, flattening, sphere positivity, and the isotropic-corner lemma.
- Route 1 additionally needs angular/projective charts, unit-clear coercivity, \(A_2\)-casting, its image-domain control, the Jacobian \(|\det M|^{-4}\), and a determinant sector/complement argument.
- Both routes still owe control of genuine outer rank degeneration.

**INFERENCE.** Route 2’s substantive remainder is therefore strictly smaller: it is the common outer-tail/good-chart or deeper \((S,J)\) rung, without Route 1’s casting-specific obligations.

**Verdict:** native wins. It reaches the same strict threshold \(c'<7/2=\tfrac12\minAdm(3,3,3,4)\), genuinely eliminates rather than relocates the determinant-inverse artifact, and—relative to the stated bank—leaves only the deeper \((S,J)\) rung shared by both routes.