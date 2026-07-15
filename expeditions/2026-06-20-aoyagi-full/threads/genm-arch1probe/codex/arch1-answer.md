## Q-A(a): deep-factor soundness

**Verdict: the explicit deep-stratum gate is unnecessary on the stated binding-cut/descent route, but `hGae` alone is not an integrability argument. The descent does the substantive work.**

- [FACT] Put \(d=\operatorname{deepTailMin}(M)\). Since the generic rank of \(Z_{\mathrm{deep}}\) is \(d\), if \(b\le d\), then
  \[
  \{z:\operatorname{rank}Z_{\mathrm{deep}}(z)<b\}
  \]
  is a proper algebraic set and hence has Lebesgue measure zero. It is not a positive-measure obstruction.

- [FACT] For such a \(z\), with \(k=\operatorname{rank}Z_{\mathrm{deep}}(z)\ge b\), the exceptional set
  \[
  \{A_{\rm cor}:\operatorname{rank}(A_{\rm cor}Z_{\mathrm{deep}})<b\}
  \]
  is also algebraic and null. Thus \(Q_bQ_b^{T}>0\) for almost every \((A_{\rm cor},z)\).

- [FACT] Nevertheless, positivity almost everywhere does not imply integrability. For fixed \(G=ZZ^T\) of rank \(k\), the standard real Wishart criterion is
  \[
  \int_{\text{bounded }N}
  \det(NGN^T)^{-a/2}\,dN<\infty
  \quad\Longleftrightarrow\quad
  a<k-b+1,
  \]
  locally across the determinantal locus.

  Indeed, after restricting to the \(k\)-dimensional range of \(G\), this is the local integrability criterion for
  \(\det(XX^T)^{-a/2}\), \(X\in\mathbb R^{b\times k}\).

- [FACT] The dependence on \(G\) is genuinely singular. Cauchy–Binet gives
  \[
  \det(X\operatorname{diag}(\lambda_i)X^T)
  =
  \sum_{|I|=b}\Bigl(\prod_{i\in I}\lambda_i\Bigr)\det(X_I)^2.
  \]
  In particular, \(G\mapsto \rho G\) multiplies the charge by \(\rho^{-ab/2}\). If the singular values of \(Z\) scale by \(\varepsilon\), the charge scales by \(\varepsilon^{-ab}\). When a limiting \(G\) has rank \(k_0<b\), a generic \(N\) gives leading blow-up \(\varepsilon^{-a(b-k_0)}\).

- [FACT] Hence a null deep rank-drop locus can still create nonintegrable neighbourhoods. `hGae` only permits the Gamma-peel identity almost everywhere.

- [FACT] If the asserted comparator estimate is established, then
  \[
  I_{\rm shell}\le
  K\,I_{\rm corner}\!\left(\operatorname{redChain}_uM,\,
  q\right),
  \qquad q=c'-\frac{ab}{2},
  \]
  and
  \[
  q<\frac{\minAdm(M)-ab}{2}
   \le \frac{\minAdm(\operatorname{redChain}_uM)}2.
  \]
  Thus the shorter-chain induction hypothesis controls precisely the degeneration as \(Z\) approaches its rank-drop strata.

- [INFERENCE] Therefore the deep-stratum gate is off-path and unnecessary provided the comparator domination is a proved lemma. If that domination is merely asserted, there is a proof gap—but the gap is not a positive-measure failure of `hGae`.

## Q-A(b): why binding strict shells satisfy the rank conditions

- [FACT] Define
  \[
  D(x)=\minAdm(x,M_2,\ldots,M_{\rm last}),\qquad
  d=\min(M_2,\ldots,M_{\rm last}).
  \]
  The recursion implies the one-step bound
  \[
  D(x+1)-D(x)\le d.
  \]
  This follows inductively: use the same recursive cut when \(d=M_2\), and increment the recursive cut when the minimum width occurs deeper.

- [FACT] Let \(t^*\) minimize
  \[
  f(t)=(M_0-t)(M_1-t)+D(t),
  \]
  and write \(a_0=M_0-t^*\), \(b_0=M_1-t^*\). A strict shell implies \(t^*+1\) is admissible. Minimality gives
  \[
  0\le f(t^*+1)-f(t^*)
   =-(a_0+b_0-1)+D(t^*+1)-D(t^*),
  \]
  hence
  \[
  a_0+b_0-1\le d.
  \]

- [FACT] At a strict shell \(u=t^*+j\), \(j\ge1\),
  \[
  a=a_0-j,\qquad b=b_0-j,
  \]
  so
  \[
  a+b\le d+1-2j\le d-1,
  \qquad b<d.
  \]
  Therefore `hGae` holds, and the generic-rank Wishart condition holds with room to spare:
  \[
  a<d-b+1.
  \]

- [FACT] This conclusion is special to binding strict shells. An arbitrary cut with \(u<M_1-d\) has \(b>d\), so \(Q_bQ_b^T\) is singular for every \(A_{\rm cor}\) on a full-measure set of deep variables. Even when \(b\le d\), an arbitrary cut need not satisfy the stronger Wishart inequality \(a<d-b+1\).

Thus binding supplies pointwise eligibility and generic \(A_{\rm cor}\)-integrability; descent supplies joint deep-factor integrability.

## Q-B(i): the quadratic normal loss

Consider the standard two-factor normal slice \(AZ=0\), with
\[
A\in\mathbb R^{p\times m},\qquad Z\in\mathbb R^{m\times q},
\]
on the rank-\((\ell,s)\) stratum. Put \(h=m-\ell-s\). After Schur coordinates one obtains the exact local model
\[
A=
\begin{pmatrix}
P&0&0\\
C_0&X&Y
\end{pmatrix},
\qquad
Z=
\begin{pmatrix}
U&V\\
R&0\\
0&W
\end{pmatrix},
\]
where \(P\in GL_\ell\) and \(R\in GL_s\) are the chosen pivots. Then
\[
AZ=
\begin{pmatrix}
PU&PV\\
C_0U+XR&C_0V+YW
\end{pmatrix}.
\]

- [FACT] The linear normal block is
  \[
  w=(\operatorname{vec}U,\operatorname{vec}X,\operatorname{vec}\widehat V)
  \in\mathbb R^{C_{\rm nor}},
  \qquad
  C_{\rm nor}=\ell q+(p-\ell)s.
  \]
  Translating \(V\) by its least-squares centre against \(YW\) is triangular and has Jacobian one.

- [FACT] Its transverse loss is
  \[
  g(w)=
  \|PU\|_F^2+\|C_0U+XR\|_F^2
  +\|P\widehat V\|_F^2+\|C_0\widehat V\|_F^2
  =\|\Lambda w\|_2^2,
  \]
  with
  \[
  \Lambda=
  \begin{pmatrix}
  I_s\!\otimes P&0&0\\
  I_s\!\otimes C_0&R^T\!\otimes I_{p-\ell}&0\\
  0&0&I_{q-s}\!\otimes P\\
  0&0&I_{q-s}\!\otimes C_0
  \end{pmatrix}.
  \]

- [FACT] Homogeneity is exact:
  \[
  g(rw)=\|\Lambda(rw)\|^2=r^2g(w).
  \]

- [FACT] \(\Lambda\) has full column rank whenever \(P\) is invertible and \(R\) has full row rank. Indeed, \(\Lambda w=0\) first gives \(U=V=0\) from \(P\), and then \(XR=0\), hence \(X=0\).

- [FACT] Therefore
  \[
  \|w\|=1\quad\Longrightarrow\quad
  g(w)\ge\sigma_{\min}(\Lambda)^2>0.
  \]

- [FACT] Merely saying the spectators are bounded is insufficient for a uniform floor. One needs the pivot singular values bounded away from zero. On a compact banked subchart this holds. At a chart boundary, \(\sigma_{\min}(\Lambda)\) may tend to zero; one must change pivot chart or pass to the lower-rank stratum.

## Q-B(ii): the biquadratic corner

- [FACT] There is a nonquadratic residual whenever
  \[
  h=m-\ell-s>0,\qquad p-\ell>0,\qquad q-s>0.
  \]
  After the \(V\)-translation it is comparable to
  \[
  g_{\rm corner}(Y,W)=\|D(YW)\|_F^2,
  \]
  where \(D\) is a fixed injective chart-dependent linear map.

- [FACT] If both \(Y\) and \(W\) are placed in one radial block, then
  \[
  g_{\rm corner}(rY,rW)=r^4g_{\rm corner}(Y,W),
  \]
  not \(r^2g_{\rm corner}(Y,W)\). It also has no positive unit-sphere floor: take \(Y=0\), \(\|W\|=1\), or vice versa.

- [FACT] More generally, scaling the linear normal block and the corner together gives mixed degrees:
  \[
  r^2g(w)+r^4g_{\rm corner}(Y,W).
  \]
  This is not degree-2 homogeneous. The extreme \((\ell,s)=(0,0)\) stratum is the pure product loss \(\|YW\|^2\), with no linear normal block at all.

- [INFERENCE] A correct architecture therefore applies the banked radial lemma only to \(w=(U,X,\widehat V)\). The \(YW\) corner must be handled by descent, or by banking one factor with an injective surviving-frame bound. Treating both \(Y\) and \(W\) as one quadratic transverse block would be unsound.