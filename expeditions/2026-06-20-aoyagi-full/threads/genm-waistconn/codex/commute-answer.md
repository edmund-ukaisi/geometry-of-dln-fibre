## 1. Verdict

**VERDICT: (b)-is-the-route — for general `FaithfulSJAt`, reversal sends \(\Gamma Q\) to \(Q^{\mathsf T}\Gamma^{\mathsf T}\), a back-oriented factorization for the effective chain \((M_L,\ldots,M_1,a)\), not automatically an admissible front-oriented decoration on \(\operatorname{rev}M\).**

Neither route is presently a completed proof: route (b) still needs a genuinely stronger spectral-decoration closure result.

## 2. Route (a): reversal

For the trivial decoration, reversal is exact. Reversing and transposing the raw layers is measure-preserving and

\[
\|\operatorname{prod}(M,A)\|_F
=
\|\operatorname{prod}(\operatorname{rev}M,A^{\mathrm{rev},\mathsf T})\|_F.
\]

For general \(D\), however,

\[
Z\simeq
\operatorname{Mat}_{a\times M_1}\times
\operatorname{Params}(M_1,\ldots,M_L),
\qquad
\operatorname{res}_D=\Gamma A_1\cdots A_{L-1}.
\]

Transposition gives

\[
(\Gamma A_1\cdots A_{L-1})^{\mathsf T}
=
A_{L-1}^{\mathsf T}\cdots A_1^{\mathsf T}\Gamma^{\mathsf T}.
\]

This is naturally parameterized by the reversed effective chain

\[
(M_L,M_{L-1},\ldots,M_1,a),
\]

whereas an admissible decoration on \(\operatorname{rev}M\) must use

\[
(M_L,M_{L-1},\ldots,M_1,M_0).
\]

Thus the endpoints already disagree unless \(a=M_0\). Moreover, the old free block becomes the final tail layer, while the new free front block must be extracted from the old tail. Transporting the carrier indices, domain equivalence, exceptional support, and Jacobian data is a new reversal-closure construction—not the plain layer reindex used for the trivial integral.

There is a special escape hatch: if one separately proves \(a=M_0\) and full compatibility of the carrier/domain presentation, then one can take

\[
\Gamma'=A_{L-1}^{\mathsf T},
\qquad
\operatorname{tail}'=(A_{L-2}^{\mathsf T},\ldots,A_1^{\mathsf T},\Gamma^{\mathsf T}).
\]

That could make reversal a block permutation. Those additional facts are not supplied by the stated `FaithfulSJAt` clause, so general decorated reversal cannot currently be invoked.

## 3. Route (b): exact obligations

Let \(r=M_1\), \(G=QQ^{\mathsf T}\), and

\[
J_c(Q)=
\int_{\Gamma\in[-1,1]^{a\times r}}
\bigl(\operatorname{tr}(\Gamma G\Gamma^{\mathsf T})\bigr)^{-c}\,d\Gamma .
\]

1. **Full-rank Gram reduction — BOUNDED labour.**

   Prove \(G>0\) almost everywhere: a maximal minor of \(Q\) is a nonzero polynomial because the waist widths permit a full-row-rank product. Then use Tonelli and an SVD/eigenvalue decomposition. The rank-deficient locus is null.

   One must preserve the shrinking eigen-directions, not simply enlarge the transformed \(\Gamma\)-domain to a fixed box.

2. **Spectral-weight admissibility — POTENTIAL WALL.**

   After integrating \(\Gamma\), the tail carries \(J_c(Q)\), or sectorwise weights involving several eigenvalues. This is not of the existing `FaithfulSJAt` form
   \[
   \|\Gamma'\operatorname{prod}(\operatorname{dropHead}T)\|^{-2s}.
   \]

   Consequently, the present universal IH does not apply merely because
   \(\minAdm(\operatorname{dropHead}M)\ge\minAdm(M)\).

   One must either:

   - prove each spectral weight is dominated by finitely many existing admissible decorations; or
   - strengthen the inductive predicate to admit rank-profile/eigenvalue weights and prove its closure.

   A blanket \(\det(G)^{-a/2}\) decoration is generally too singular.

3. **Front/deep charge split — POTENTIAL WALL.**

   Near a rank-\(q\) tail, the \(q\) strong singular directions contribute front budget \(aq/2\). The remaining rank-defect weight must consume only

   \[
   c-\frac{aq}{2}.
   \]

   If \(d_q(T)/2\) denotes the tail budget available on that rank stratum, the required arithmetic is

   \[
   \minAdm(M)\le aq+d_q(T)
   \qquad\text{for every relevant }q.
   \]

   The known scalar inequality
   \[
   \minAdm(T)\ge\minAdm(M)
   \]
   does not establish these rank-profile inequalities.

For ordered eigenvalues \(0<\lambda_1\le\cdots\le\lambda_r\), the required fibre estimate is approximately

\[
J_c(Q)\lesssim
\left(\prod_{i=r-k+1}^{r}\lambda_i^{-a/2}\right)
\lambda_{r-k}^{-(c-ka/2)}
\]

when \(ka/2<c<(k+1)a/2\), with logarithms at equality. This refined, \(c\)-dependent weight is the object the tail induction must support.

## 4. Worked waist: \((3,2,3,4)\)

Exactly,

\[
\minAdm(2,3,4)=\min\{6,\;2+4,\;8\}=6,
\]

and

\[
\minAdm(3,2,3,4)
=\min\{6,\;2+\minAdm(1,3,4),\;6\}
=\min\{6,5,6\}=5.
\]

Thus the target is \(c<5/2\), while the tail threshold is \(c<3\).

For the natural \(a=3\), write \(0<\lambda_1\le\lambda_2\). Then

\[
J_c(Q)\lesssim
\begin{cases}
\lambda_2^{-c},&c<3/2,\\[2mm]
\lambda_2^{-3/2}\lambda_1^{-(c-3/2)},&3/2<c<5/2.
\end{cases}
\]

Hence the weak-eigenvalue exponent is \(c-3/2<1\).

By contrast, the crude determinant bound gives

\[
\det(G)^{-3/2}
=\lambda_1^{-3/2}\lambda_2^{-3/2}.
\]

Near a generic rank-one \(2\times4\) matrix, the rank-one locus has codimension \(3\) and
\(\lambda_1\simeq\operatorname{dist}^2\). The crude weight behaves like
\(\operatorname{dist}^{-3}\), giving logarithmic divergence. So the det-only reduction is provably too strong; the refined eigenvalue split is essential.

As a sanity check, \((2,1,2,2)\) is easy: both minima equal \(2\), and

\[
\|\Gamma Q\|_F^2=\|\Gamma\|^2\|Q\|^2.
\]

For \(c<1\), the \(\Gamma\)-integral and the tail IH both converge directly.

## 5. Most likely break

The likely failure point is **proving that the \(c\)-dependent eigenvalue/rank-profile weight is an admissible tail decoration**. Without that closure theorem, route (b) stops before the IH, and \(\minAdm(\operatorname{dropHead}M)\ge\minAdm(M)\) does not repair the gap.