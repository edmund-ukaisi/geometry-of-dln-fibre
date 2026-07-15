Put
\[
\alpha=d-a\ge1,\qquad \beta=\alpha-u=d-a-u,\qquad
C_s=ub+(M_0-s)(u-s)+sd.
\]
The displayed \(C_{\ell,s}\) simplifies exactly to \(C_s\); the \(\ell\)-dependence cancels.

### Q-A1 — DIVERGENT for the enlarged bound; the original tube need not diverge

[FACT] The Jacobians are correct:

\[
dA=|\det D|^d\,dD\,dX,\qquad
\det(AA^\top)^{-a/2}=|\det D|^{-a}\det(I+XX^\top)^{-a/2},
\]
and, row by row,
\[
dB=|\det D|^{-u}\,dH.
\]

Thus enlargement to all \(H\in\mathbb R^{ub}\) leaves \(|\det D|^\beta\).

For ordered singular values \(0<\sigma_1<\cdots<\sigma_b\),
\[
dD\asymp \prod_{i<j}|\sigma_j^2-\sigma_i^2|\,d\sigma\,d\mu.
\]
On a standard sector the raw singular-value exponents are
\[
e_i=\beta+2(i-1).
\]
The exact condition for the first \(k\) singular values to vanish jointly is
\[
\sum_{i=1}^k(e_i+1)=k(\beta+k)>0,
\]
equivalently \(\beta>-k\). For every \(k\), this is equivalent to the rank-one condition
\[
\boxed{\beta>-1}.
\]

Equivalently, the \(k\)-fold exceptional radial variable has exponent
\[
k(\beta+k)-1.
\]

At \(d=a+1,\ u=2,\ b=2\),
\[
\beta=-1,\qquad (e_1,e_2)=(-1,1).
\]
The rank-one exponent is \(-1\): logarithmic divergence. The rank-two exponent is
\[
2(-1+2)-1=1,
\]
so the divergence is specifically transverse to the rank-\((b-1)\) divisor.

Hence the enlargement creates a divergent majorant. Scope \(d\ge a+1\) does not make it integrable; enlargement requires \(d\ge a+u\).

### Q-A2 — FINITE, but the proposed two-region argument is false as stated

[FACT] On \(\|D\|\lesssim\tau\),
\[
\int_{R_D}(\|H\|^2+\tau^2)^{-q}dH
\le C|\det D|^u\tau^{-2q}.
\]
Therefore the determinant weight becomes
\[
|\det D|^\alpha\tau^{-2q}.
\]
Homogeneity gives
\[
\int_{\|D\|\le\tau}|\det D|^\alpha\,dD
\asymp\tau^{b^2+b\alpha}.
\]
At a \(Y\!W\)-stratum with
\[
N_s=C_s-ub=(M_0-s)(u-s)+sd,
\]
this region has radial condition
\[
\boxed{2q<N_s+b^2+b\alpha}.
\]

On \(\|D\|\gtrsim\tau\), however, \(\det D\) is not bounded below. The set contains matrices with
\[
\sigma_1\to0,\qquad \sigma_2,\ldots,\sigma_b\asymp1.
\]
The full-space estimate still leaves \(|\det D|^\beta\), which is nonintegrable whenever \(\beta\le-1\). Thus the quoted “large-\(D\)” assertion is false.

The correct retained-tube split is singular-value-wise. If exactly \(k\) singular values satisfy \(\sigma_j\le\tau\), then
\[
\int_{R_D}(\|H\|^2+\tau^2)^{-q}dH
\lesssim
\left(\prod_{j\le k}\sigma_j^u\right)
\tau^{u(b-k)-2q}.
\]
After multiplication by \(|\det D|^{\alpha-u}\), short singular values have exponent \(\alpha\), while long ones retain exponent \(\alpha-u\).

In the named borderline \((\alpha,u,b)=(1,2,2)\):

\[
\begin{array}{c|c}
k&\text{\(\tau\)-order after \(D\)-integration}\\ \hline
0&\tau^{4-2q}\log(1/\tau)\\
1&\tau^{4-2q}\\
2&\tau^{6-2q}.
\end{array}
\]
Thus the worst order is the desired \(\tau^{ub-2q}\), up to one harmless logarithm.

For general parameters one must also retain the \(P\)-\(U\) coupling. Let \(p=\operatorname{rank}P\), \(s=\operatorname{rank}Y\), and let \(k=b-\operatorname{rank}D\). Then:

- the rank-\(D\) normal codimension plus charge is \(k^2+\alpha k\);
- \(PU+BD\) has image dimension
  \[
  ub-k(u-p);
  \]
- inside the rank-\(Y=s\) stratum, imposing \(\operatorname{rank}P=p\) costs
  \[
  (s-p)(u-p).
  \]

Hence the exact weighted candidate is
\[
T_{s,p,k}
=
C_s+(s-p)(u-p)+k(k+\alpha-u+p).
\]

Writing \(h=s-p\), \(t=u-p\):

- if \(k\le h\),
  \[
  T_{s,p,k}-C_s=t(h-k)+k(k+\alpha)\ge0;
  \]
- if \(h\le k\le t\),
  \[
  T_{s,p,k}-C_{p+k}=h(h+\alpha)+t(k-h)\ge0;
  \]
- if \(k>t\), directly \(T_{s,p,k}\ge C_s\).

Therefore
\[
\boxed{T_{s,p,k}\ge\min_r C_r}.
\]
The given strict gate \(2q<\min_r C_r\) makes every joint radial integral converge. Thus \(I_{\rm leaf}<\infty\).

### Q-A3 — FINITE by a cleaner joint convolution estimate

[FACT] A useful compressed route is to keep both \(U\) and \(B\). For
\[
L_{P,D}(U,B)=PU+BD,
\]
one has
\[
L_{P,D}L_{P,D}^{*}
=
I_b\otimes PP^\top+D^\top D\otimes I_u.
\]
If \(p_i,\sigma_j\) are the singular values of \(P,D\), its eigenvalues are
\[
p_i^2+\sigma_j^2.
\]
The pushforward density is bounded by
\[
C\prod_{i=1}^u\prod_{j=1}^b(p_i^2+\sigma_j^2)^{-1/2}.
\]
Consequently, for \(2q>ub\),
\[
\int_{U,B}(\|PU+BD\|^2+\tau^2)^{-q}
\lesssim
\tau^{ub-2q}
\prod_{i,j}(p_i^2+\sigma_j^2)^{-1/2}.
\]
Its rank-stratum exponents are exactly \(T_{s,p,k}\) above.

So a full geometric tube construction is unnecessary. A scalar bound using only \(\operatorname{vol}(R_D)\) is generally too crude; the singular-value or covariance coupling is essential. No single separated monomial bound handles the cancellations in \(PU+BD\).

### Q-B1 — FINITE reduction algebraically, but not row-space invariance

[FACT] Write
\[
Z=\widetilde S\,\widetilde O,\qquad
\widetilde O\widetilde O^\top=I_\rho,
\]
and set
\[
\widehat Q_p=z_0\widetilde S,\qquad
\widehat Q_b=A\widetilde S.
\]
Then
\[
Q_bQ_b^\top=\widehat Q_b\widehat Q_b^\top,
\qquad
\Pi_b=\widetilde O^\top\widehat\Pi_b\widetilde O.
\]
If
\[
\widehat R=\widehat Q_p+P^{-1}B\widehat Q_b,
\]
then
\[
\widehat R\widetilde O(I-\Pi_b)
=
\widehat R(I-\widehat\Pi_b)\widetilde O.
\]
Since right multiplication by \(\widetilde O\) preserves Frobenius norm,
\[
\|C\widehat R(I-\widehat\Pi_b)\widetilde O\|_F
=
\|C\widehat R(I-\widehat\Pi_b)\|_F.
\]
Thus the \(\rho\)-dimensional leaf identity is exact.

But “depends only on the row space of \(Z\)” is false. Replacing \(Z\) by \(tZ\) preserves its row space but scales every \(Q\). The singular values in \(\widetilde S\) survive through the pushforward density.

### Q-B2 — DIVERGENT in general; the first-rank-drop charge itself is finite

[FACT] For \(u+b\) independent rows, the image density has height of order
\[
\det(\widetilde S^\top\widetilde S)^{-(u+b)/2}.
\]
Its support does not blow up in collapsing directions; it shrinks. Density height alone therefore proves neither convergence nor divergence.

For fixed effective rank \(r\), the corank-charge integral has SVD exponents
\[
r-b-a+2(i-1).
\]
The exact condition is
\[
\boxed{r\ge a+b}.
\]
Thus:

- at the first drop \(r=\rho-1\), scope gives \(r\ge a+b\), so the charge remains integrable;
- at \(r=a+b\), the first exponent is \(0\), still finite;
- at \(r=a+b-1\), it is \(-1\), logarithmically divergent;
- at \(r=b\), it is \(-a\le-1\), divergent;
- below \(b\), the Gram determinant vanishes a.e.

So the assertion that trouble begins only when \(\operatorname{rank}Z<b\) is incorrect for uniform integration in \(A\).

More importantly, the loss already creates a first-drop wall. Let \(\kappa\) be the normal codimension of a smooth tail stratum \(\operatorname{rank}Z=\rho-1\). Since
\[
C_s(\rho-1)=C_s(\rho)-s,
\]
the combined candidate is
\[
\boxed{C_s(\rho)-s+\kappa}.
\]
The Part-A gate \(2q<C_s(\rho)\) does not imply convergence when \(\kappa<s\).

### Q-B3 — DIVERGENT in general: explicit allowed counterexample

[FACT] Take
\[
u=2,\quad a=1,\quad b=1,\quad \rho=3,\quad d=2,
\]
and let the tail be one freely varying \(3\times3\) matrix. Then
\[
a+b=2=\rho-1.
\]
The leaf codimensions are
\[
C_0=8,\qquad C_1=C_2=6.
\]
Thus every \(q<3\) passes the stated Part-A gate.

Near a smooth rank-two tail matrix, such as \(\operatorname{diag}(1/2,1/2,0)\), rank loss has one transverse coordinate \(t\), so \(\kappa=1\). On the regular front stratum \(s=u=2\), take:

- \(P\) uniformly invertible;
- the \(A\)-pivot bounded away from zero, so the corank charge is bounded;
- the lost transverse \(W\)-column in an annulus.

After smooth shears the loss is comparable to
\[
|H|^2+|W_{\rm surviving}|^2+t^2|W_{\rm lost}|^2.
\]
Holding \(W_{\rm lost}\) in that annulus leaves
\[
|y|^2+t^2,
\qquad y\in\mathbb R^{ub+u(d-1)}=\mathbb R^4.
\]
Hence the local integral contains
\[
\int_{\mathbb R^4\times\mathbb R}
(|y|^2+t^2)^{-q}\,dy\,dt,
\]
which diverges exactly when
\[
2q\ge5.
\]

For example,
\[
q=\frac{11}{4}
\]
satisfies the leaf gate \(2q=5.5<6\), but the general-depth integral diverges.

For a rank drop by \(k\) with tail-normal codimension \(\kappa_k\), the necessary additional gate suggested by the same local model is
\[
\boxed{2q<C_s(\rho-k)+\kappa_k
      =C_s(\rho)-ks+\kappa_k}.
\]

The most likely failure is therefore a codimension-one rank drop in a square bottleneck tail layer: it replaces \(u\) regular leaf directions by one tail-normal direction. It is not the corank charge; it is the loss degeneration at \(\rho\to\rho-1\).