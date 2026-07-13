### 1. Verdict

[INFERENCE, high confidence] **HEAVY-NEW-MODULE-WALL** for the literal eigenvalue-density brick: generic Euclidean CoV does not supply the non-injective SVD quotient, Stiefel/frame measure, repeated-spectrum handling, or Vandermonde density.

### 2. Cheapest route

[INFERENCE] Ranking:

1. **(ii) Scalar max-pivot Schur-flag recursion — MODERATE-NEW-MODULE.**
2. **(iii) Sharp singular-shell volume bounds** proved by sector blowups—essentially (ii) behind a different interface.
3. **(i) Rectangular-SVD/Wishart density — HEAVY wall.**

The hardest obligation for (ii) is one dimension-uniform sector substitution lemma with Jacobian \(|p|^{s+z-2}\), bounded transformed boxes, and residual loss comparable to the \((s-1)\times(z-1)\) problem. Only generic `MeasureTheory.Function.Jacobian` CoV [likely-exists; supplied recon says banked] is available; a Schur-sector/Jacobian theorem is absent.

### 3. The \((3,2,3)\) chart

[FACT] Yes—it is one ordinary six-dimensional CoV. On \(p\ne0\),
\[
\Phi(p,t_1,t_2,\ell,w_1,w_2)=
\begin{pmatrix}
p&pt_1&pt_2\\
\ell p&w_1+\ell pt_1&w_2+\ell pt_2
\end{pmatrix}.
\]
Its inverse is \(t_i=a_{1,i+1}/p,\ \ell=a_{21}/p,\ w_i=a_{2,i+1}-\ell a_{1,i+1}\), and
\[
|\det D\Phi|=|p|^3.
\]
The raw Schur map using \(r_i=pt_i\) has Jacobian \(|p|\); \(r=pt\) contributes \(|p|^2\), yielding \(h_1=3\).

On the max-pivot sector, \(t,\ell,w/p\) are bounded. Writing the columns of \(A_0\) as \(u,v\), a determinant-one translation in \(u\) orthogonalizes
\[
(u+\ell v)\,p(1,t)+v(0,w),
\]
giving loss uniformly comparable to \(p^2\|u'\|^2+\|w\|^2\|v\|^2\). Thus the deciding chart works; route (c) is moderate, not heavy.

### 4. General \(L\)

[FACT] A recursion that removes one end layer terminates at three widths; it never needs to stratify the deep product itself.

[INFERENCE] Therefore the reduction is sound provided every non-base branch produces an admissible decoration accepted by the stated strong IH. The refuted “better end” claim shows that the waist base is unavoidable, not that arity recursion fails. The remaining risk is decoration/threshold bookkeeping, not another analytic resolution wall.

### 5. First target and charge identity

[INFERENCE] Bank the identity, but the \(2\times3\) sector-CoV lemma is the better first de-risking target.

[FACT] Put \(g(k)=kx+(s-k)(z-k)\). Then
\[
g(k+1)-g(k)=x-(z+s-2k-1).
\]
Hence \(g\) decreases precisely while the next arithmetic-series term exceeds \(x\). At the crossing,
\[
\min_k g(k)=kx+\sum_{j=k+1}^s(z+s+1-2j)
=\sum_{j=1}^s\min(x,z+s+1-2j).
\]

### 6. Cheapest decisive test

[INFERENCE] Compile a scratch theorem giving the exact CoV for the displayed \(\Phi\), restricted by an indicator to one max-pivot sector, with density \(|p|^3\). Include the two uniform loss inequalities. If that works without new general measure theory, the step-2 bypass is decisively **MODERATE**; do not begin the SVD module.