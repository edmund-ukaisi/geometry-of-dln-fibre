## Verdict

The joint method reaches the target, with one qualification: it must be the full nested determinantal resolution, not a single split by the rank of one intermediate matrix.

The necessary rank flag is
\[
j=\operatorname{rank}A_0,\qquad r=\operatorname{rank}(A_0A_1).
\]
Applied before forming the factored charge or pointwise density majorant, it has no exponent residual.

| Cell | Target | Joint resolution | Residual |
|---|---:|---:|---:|
| \((2,1,2,2)\), \(u=0\) | \(1\) | \(1\) | \(0\) |
| \((2,2,3,3)\), \(u=0\) | \(2\) | \(2\) | \(0\) |
| saturated \((2,2,2,2)\), \(u=2\) | \(3/2\) | \(3/2\) | \(0\) |

For the saturated cell, the naive density fold reaches only \(1\), so its artificial residual is \(1/2\). The joint resolution recovers it.

For both deep cells, \(ab/2\) already equals the target. Thus divergence of the auxiliary angular integral at the endpoint does not constitute a positive undershoot.

## PROVEN: rank-sector exponents

For a fixed flag \((j,r)\), the true-Jacobian exponent numerator is
\[
D_{j,r}
 =(M_0-j)(M_1-j)
 +(j-r)(M_2-r)
 +rM_3,
\]
where
\[
0\le j\le \min(M_0,M_1),\qquad
0\le r\le \min(j,M_2).
\]

The three terms come from:

1. the rank-\(j\) determinantal normal block of \(A_0\);
2. the rank-\(r\) determinantal normal block of the active \(j\times M_2\) part of \(A_1\);
3. the \(rM_3\) independent equations imposed by \((A_0A_1)A_2=0\) once \(\operatorname{rank}(A_0A_1)=r\).

Standard Schur big-cell coordinates have unit Jacobian in the tangential variables, while polarizing the normal blocks gives precisely these dimensions. Hence the flag contributes
\[
\lambda_{j,r}=\frac{D_{j,r}}2.
\]

If \(r\) denotes only the rank of the intermediate product, its exponent is
\[
\boxed{
\lambda_r
=\frac12\left[
rM_3+
\min_{r\le j\le\min(M_0,M_1)}
\bigl((M_0-j)(M_1-j)+(j-r)(M_2-r)\bigr)
\right].
}
\]

Now
\[
\begin{aligned}
\min_{j,r}D_{j,r}
&=\min_j\left[
(M_0-j)(M_1-j)
+\min_r\bigl((j-r)(M_2-r)+rM_3\bigr)
\right]\\
&=\min_j\left[
(M_0-j)(M_1-j)+\operatorname{minAdm}(j,M_2,M_3)
\right]\\
&=\operatorname{minAdm}(M).
\end{aligned}
\]

Thus
\[
\boxed{\min_r\lambda_r=\frac12\operatorname{minAdm}(M).}
\]

This is the exact correspondence with the two levels of the `minAdm` recursion: \(j\) is its outer choice and \(r\) its inner choice.

At a rank-\(u\) front chart, writing \(j=u+h\), the corresponding expression is
\[
D^{(u)}_{h,r}
=(a-h)(b-h)+(u+h-r)(M_2-r)+rM_3.
\]

## Explicit cells

For \(M=(2,1,2,2)\):
\[
D_{0,0}=2,\qquad D_{1,0}=2,\qquad D_{1,1}=2.
\]
Both intermediate-rank sectors therefore contribute \(1\). The target is \(1\).

For \(M=(2,2,3,3)\):
\[
\begin{array}{c|cccccc}
(j,r)&(0,0)&(1,0)&(1,1)&(2,0)&(2,1)&(2,2)\\ \hline
D_{j,r}&4&4&4&6&5&6
\end{array}
\]
Hence
\[
(\lambda_0,\lambda_1,\lambda_2)=(2,2,3),
\]
and the minimum is \(2\).

For the saturated \(M=(2,2,2,2)\):
\[
\begin{array}{c|cccccc}
(j,r)&(0,0)&(1,0)&(1,1)&(2,0)&(2,1)&(2,2)\\ \hline
D_{j,r}&4&3&3&4&3&4
\end{array}
\]
Thus
\[
(\lambda_0,\lambda_1,\lambda_2)=\left(\frac32,\frac32,2\right).
\]
The binding sectors are \((j,r)=(1,0),(1,1),(2,1)\), giving the target \(3/2\).

Here
\[
A=1,\qquad 2\Delta=0,
\]
so the pointwise density argument reaches only
\[
\frac32-\left(\frac12-0\right)=1.
\]
Its residual \(1/2\) is entirely recovered by the joint rank sectors.

Although the saturated chart has \(P\) invertible almost everywhere, the \(j<2\) sectors remain as boundary exceptional divisors when \(P\) approaches rank deficiency. Removing the exact determinantal set, which has measure zero, does not remove its surrounding divergence.

## Why the naive methods undershoot

They compute different auxiliary integrals produced by lossy operations.

- The deep-corank factorization demands independent integrability of the endpoint angular charge \(J\). This separates the small angular factor from the determinantal Jacobian of the accompanying rank drop.
- The saturated pointwise estimate replaces the exact pushforward density by its worst radial order and then folds that order uniformly into the loss. It treats “\(z\) is low rank” and “the tail is singular” as freely simultaneous, discarding their joint codimension.

Thus these bounds overestimate the singularity of the original integral. Their smaller thresholds are genuine thresholds of the auxiliary majorants, not a second RLCT of \(F\).

In particular, endpoint divergence is not an undershoot: RLCT finiteness only requires \(c<\lambda\). In the two deep test cells,
\[
ab/2=\lambda,
\]
so failure at \(c=\lambda\) is compatible with exact attainment.

## Q4: induction suffices

The shorter chains are
\[
N_j=(j,M_2,M_3),\qquad 0\le j\le\min(M_0,M_1).
\]
At a local rank-\(u\) chart these are initially \(j=u+h\); boundary compactification, especially in the saturated case, also produces lower \(j\).

Put
\[
d_j=(M_0-j)(M_1-j),\qquad
m_j=\operatorname{minAdm}(j,M_2,M_3),\qquad
m=\operatorname{minAdm}(M).
\]
Because
\[
m\le d_j+m_j,
\]
for every \(c<m/2\), integrating the \(d_j\)-dimensional determinantal normal block leaves residual exponent
\[
q_j=\max\left(0,c-\frac{d_j}{2}\right)<\frac{m_j}{2}.
\]
At equality \(c=d_j/2\), only a logarithm appears and can be absorbed by an arbitrarily small exponent.

Therefore the IH giving finiteness for every arity-3 chain below its own \(m_j/2\) closes every sector. No sector asks its reduced chain for more than that chain supplies.

## ARGUED qualification

The exponent calculation and IH budget are exact. What is not supplied merely by saying “stratify by rank” is the analytic atlas: one must actually use the nested \((j,r)\) Schur/determinantal charts, retain their Jacobians, and apply them before the lossy marginal bounds. A one-stage rank-\(r\) split without resolving the product-map preimage in \(j\) is incomplete, but that is a missing construction—not an exponent obstruction.