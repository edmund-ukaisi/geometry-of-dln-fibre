## (a) Joint \(B_{12}\)-integration

**PROVEN: it does not factor cleanly.** Put \(s=c'-a/2\) and \(\Pi=\omega^{\mathsf T}\omega\). Orthogonality gives

\[
\widetilde Q=v\omega+Q_p(I-\Pi),\qquad
W=\|Pv\|^2+D,
\]

where \(D=\|PQ_p(I-\Pi)\|_F^2\). With

\[
x=Pv=PQ_p\omega^{\mathsf T}+\sigma B_{12},
\]

the exact integral is

\[
\int_{\Box}\|v\|_\infty^{-a}W^{-s}\,dB_{12}
=
\sigma^{-u}\!
\int_{x_0+\sigma\Box}
\|P^{-1}x\|_\infty^{-a}(D+\|x\|^2)^{-s}\,dx .
\]

The domain is a translated, \(\sigma\)-shrinking box. Thus \(\sigma^{-u}\) does not cancel as an independent finite factor. Also,

\[
\int_{\mathbb R^u}\|v\|^{-a}dv
\]

never converges globally: \(a<u\) gives only local integrability at \(0\).

In the bounded-width arm \(M_2\le b=1\), necessarily \(M_2=1\). Write

\[
Q=\binom y\eta R,\qquad H=Py+B_{12}\eta .
\]

Then exactly

\[
v=\operatorname{sgn}(\eta)\|R\|P^{-1}H,\qquad
W=\|R\|^2\|H\|^2,
\]

so

\[
\|v\|_\infty^{-a}W^{-s}
=
\underbrace{\|R\|^{-a}\|P^{-1}H\|_\infty^{-a}}_{D_{\mathrm{inc}}}
\,W^{-s}.
\]

The leftover is therefore the coupled conditioning weight

\[
\boxed{D_{\mathrm{inc}}
=\|R\|^{-a}\|P^{-1}H\|_\infty^{-a}}.
\]

On a well-conditioned \(P\)-chart it is Gram-equivalent to

\[
\det(RR^{\mathsf T})^{-a/2}\det(H^{\mathsf T}H)^{-a/2}.
\]

## (b) The \(\|Q_b\|^{-u}\) factor

**PROVEN: if emitted, it is a decoration.** Extending the moving box to \(\mathbb R^u\) leaves

\[
\sigma^{-u}=\|Q_b\|^{-u}.
\]

A qbox could remove this only if \(Q_b\) were itself a free \(1\times q\) row and \(u<q\). Here \(Q_b\) is a product row, so no such direct qbox applies; peeling a factor transfers conditioning elsewhere.

Moreover, \(\sigma^{-u}\) is not the principal obstruction. Restricting \(\sigma\) bounded away from zero still leaves the singularity at \(H=v=0\), where the same \(B_{12}\)-directions also make \(W=0\).

## (c) Net classification

**PROVEN.** `edge_C_shift_bound` and `scaledRadialEuclid` are individually valid, but together emit \(D_{\mathrm{inc}}W^{-s}\). `frontCollapse` and plain hIH control only \(W^{-s}\); neither controls the shared incidence factor. No independent qbox removes it.

**VERDICT: DECORATED — leftover \(D_{\mathrm{inc}}=\|R\|^{-a}\|P^{-1}H\|_\infty^{-a}\); smallest genuine product-row countercell \(M=(3,3,1,3)\), \((a,u,b)=(1,2,1)\).**

Here

\[
\minAdm(M)=3,\quad
\peelCharge(2)=1,\quad
\minAdm(\redChain 2\,M)=\minAdm(2,1,3)=2.
\]

Take \(1<c'<3/2\), so \(s=c'-1/2<1\) and plain hIH applies. Restrict \(P,\eta,R\) away from degeneracy and choose \(y\) so \(H=0\) lies inside the \(B_{12}\)-box. Then

\[
\int_{\|H\|<\delta}D_{\mathrm{inc}}W^{-s}\,dH
\asymp
\int_0^\delta r^{1-2c'}\,dr
=\infty,
\]

whereas plain front-collapse gives \(\int_0^\delta r^{1-2s}dr<\infty\).

Cheapest discriminating computation: this two-dimensional \(H\)-integral. Retaining \(\gamma\) instead gives three normal directions \((H,\gamma)\), finite precisely for \(c'<3/2\); hence the sound route must retain the joint \((H,\gamma)\) incidence coupling.