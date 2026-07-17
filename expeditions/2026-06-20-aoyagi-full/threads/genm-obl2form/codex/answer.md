THRESHOLD-LOWERED.

- [EXACT] For a free \(Q\in\mathbb R^{n\times q}\), the integral is finite exactly when
  \[
  a<q-n+1.
  \]
  Near the rank-\((n-1)\) stratum, the normal dimension is \(q-n+1\), while \(\det(QQ^\top)\) vanishes quadratically, giving the stated radial power count.

- [EXACT] For \(Q=LR\), with \(L\in\mathbb R^{n\times n}\) and \(R\in\mathbb R^{n\times q}\),
  \[
  \det(QQ^\top)
  =\det(LRR^\top L^\top)
  =\det(L)^2\det(RR^\top).
  \]
  Hence
  \[
  \det(QQ^\top)^{-a/2}
  =|\det L|^{-a}\det(RR^\top)^{-a/2}.
  \]

  The pullback acquires the divisor
  \[
  D_L=\{\det L=0\}.
  \]
  Its smooth corank-one part has codimension \(1\). There \(\det L\) vanishes transversely to order \(1\), so \(\det(QQ^\top)\) vanishes to order \(2\). Thus, with \(s=a/2\) and \(k=2\),
  \[
  sk=a<1.
  \]
  Therefore
  \[
  \int |\det L|^{-a}\,dL<\infty
  \quad\Longleftrightarrow\quad a<1.
  \]

- [EXACT] Because the parameter box is a product, Tonelli gives
  \[
  J=
  \left(\int |\det L|^{-a}\,dL\right)
  \left(\int\det(RR^\top)^{-a/2}\,dR\right).
  \]
  The second factor requires \(a<q-n+1\), while the first requires \(a<1\). Since \(q\ge n\),
  \[
  \boxed{J<\infty\iff a<1.}
  \]
  For the stipulated integer \(a\ge1\), \(J\) is always divergent. This is strictly lower than the free threshold when \(q>n\); when \(q=n\), both thresholds equal \(1\).

- [EXACT] The multiplication map is not uniformly submersive along the rank-drop preimage. Its differential is
  \[
  D\mu_A(H_1,\ldots,H_\ell)
  =\sum_i(A_1\cdots A_{i-1})H_i(A_{i+1}\cdots A_\ell).
  \]
  Some rank-drop points are submersive—for example, in \(LR\), if \(L\) is invertible, varying \(R\) realizes every perturbation of \(Q\).

  But at a singular \(L\), the cokernel of
  \[
  (H,K)\longmapsto HR+LK
  \]
  consists of matrices \(X\) satisfying
  \[
  L^\top X=0,\qquad XR^\top=0,
  \]
  and has dimension
  \[
  \operatorname{corank}(L)\bigl(q-\operatorname{rank}(R)\bigr).
  \]
  Thus for \(q>n\), a singular \(L\) gives a genuinely critical rank-drop branch even when \(R\) has full row rank.

- [EXACT] The pushforward measure consequently need not have a bounded density relative to free-matrix Lebesgue measure near rank drop. In the square-\(L\) case its density formally contains
  \[
  p(Q)=\int |\det L|^{-q}\,
  \mathbf 1_{\{L^{-1}Q\text{ lies in the }R\text{-box}\}}\,dL,
  \]
  displaying the singular contribution from nearly singular \(L\). For \(q>n\), boundedness near the generic rank-drop boundary would contradict the divergence above while the free integral remains finite.

- [EXACT] Peeling one factor does not reduce the problem to the single free-matrix Wishart bound. Here the peel leaves the residual factor
  \[
  \int|\det L|^{-a}\,dL,
  \]
  and that residual boundary already forces \(a<1\). A valid induction would have to track these degenerating prefix/suffix factors and their critical loci; applying only \(a<q-n+1\) at each peel misses the divergence.

- [EXACT] If an intermediate width is \(<n\), then \(\det(QQ^\top)\equiv0\), so \(J=\infty\) for every \(a>0\).