## Q1

**VERDICT: No. SPEC does not directly control the determinant weight for \(b>1\). The only exact coincidence occurs at \(b=1\).**

Put
\[
S=QQ^{\mathsf T},\qquad \lambda_1,\ldots,\lambda_b\ge 0.
\]
Then
\[
\det(S)^{-a/2}=\prod_{i=1}^b\lambda_i^{-a/2},
\qquad
\operatorname{frobSq}(Q)^{-c'}
 =\Bigl(\sum_{i=1}^b\lambda_i\Bigr)^{-c'}.
\]

At the homogeneous exponent \(c'=ab/2\), AM–GM gives
\[
\det(S)\le \left(\frac{\operatorname{tr}S}{b}\right)^b,
\]
hence
\[
\det(S)^{-a/2}
 \ge b^{ab/2}\operatorname{frobSq}(Q)^{-ab/2}.
\]
This is the wrong direction: the determinant singularity dominates the trace singularity.

There is no reverse bound. For
\[
Q_\delta=\operatorname{diag}(1,\ldots,1,\delta)
\]
we have
\[
\det(Q_\delta Q_\delta^{\mathsf T})^{-a/2}=\delta^{-a}\to\infty,
\qquad
\operatorname{frobSq}(Q_\delta)\to b-1.
\]
Thus no inverse Frobenius power can upper-bound the determinant weight near a rank-\((b-1)\) matrix.

When \(b=1\),
\[
\det(QQ^{\mathsf T})=\operatorname{tr}(QQ^{\mathsf T})
=\operatorname{frobSq}(Q),
\]
so SPEC matches with \(c'=a/2\). This is the only direct match.

Reducing \(b>1\) to \(b=1\) factors requires at least
\[
\det\operatorname{Gram}(q_1,\ldots,q_b)
 =\prod_{i=1}^b
 \left\|q_i-\operatorname{proj}_{\langle q_1,\ldots,q_{i-1}\rangle}q_i\right\|^2.
\]
That is already a determinant factorisation—equivalently an iterated Schur-complement/Cholesky identity. A QR change of variables merely moves the same determinant information into its Jacobian.

So an iteration of SPEC cannot even begin from \(W_{\rm enn}\) without a new bridge from the full determinant to scalar quadratic losses.

## Q2

**VERDICT: The PSD projection gives an exact but strictly weaker criterion**
\[
\boxed{a<M_2-j-b+1}.
\]
**It does not reproduce the design criterion or shrink the corner.**

Let \(d=M_2-j\), let \(U_s\) contain the strong right-singular directions, and set
\[
\Pi_s=U_sU_s^{\mathsf T}.
\]
The shell hypothesis gives
\[
ZZ^{\mathsf T}\succeq \varepsilon^2\Pi_s.
\]
Therefore
\[
\det(AZZ^{\mathsf T}A^{\mathsf T})
 \ge \varepsilon^{2b}\det(A\Pi_sA^{\mathsf T})
 =\varepsilon^{2b}\det(BB^{\mathsf T}),
\qquad B=AU_s\in\mathbb R^{b\times d}.
\]
After rotating the \(A\)-coordinates and enlarging the rotated cube to a fixed cube, the weak \(A\)-coordinates contribute only a bounded volume. What remains is
\[
\int_{B\in\text{bounded box}}
 \det(BB^{\mathsf T})^{-a/2}\,dB.
\]

Its exact local-integrability criterion is
\[
a<d-b+1.
\]
Indeed, near a generic rank-\((b-1)\) matrix, the rank-deficient locus has codimension
\[
k=d-b+1,
\]
and
\[
\det(BB^{\mathsf T})\asymp r^2
\]
in the \(k\) normal variables. The radial integral is
\[
\int_0^\eta r^{k-1-a}\,dr
 =\int_0^\eta r^{d-b-a}\,dr,
\]
which converges exactly when \(a<d-b+1\); equality gives logarithmic divergence. QR gives the same sufficient condition at all lower-rank strata.

Substituting \(d=M_2-j\) gives the crude condition
\[
\boxed{a<M_2-b-j+1}.
\]

The target after corner shrink has
\[
a'=a-j,\qquad b'=b-j,\qquad d'=M_2-j,
\]
so its codimension is
\[
d'-b'+1=M_2-b+1
\]
and its condition is
\[
\boxed{a-j<M_2-b+1}.
\]
Expressed in terms of \(a\), the crude and designed thresholds differ by \(2j\):
\[
a<M_2-b-j+1
\quad\text{versus}\quad
a<M_2-b+j+1.
\]

This is not merely a weakness of the estimate. If all \(j\) weak eigenvalues tend monotonically to zero and
\[
a\ge M_2-b-j+1,
\]
the limiting projected integral is infinite; monotone convergence then gives
\[
W_{\rm enn}(Z_\delta)\longrightarrow\infty.
\]
Thus \(W_{\rm enn}\) itself cannot be uniformly bounded in this range. A successful proof must pass a singular weight into the deeper integration or avoid completing the \(\Gamma\)-integration.

Neither PSD monotonicity nor SPEC changes \(b\) or changes the determinant exponent from \(a/2\) to \((a-1)/2\). The required simultaneous shrink
\[
(a,b)\mapsto(a-1,b-1)
\]
needs a pivot/Schur-complement mechanism coupling one \(A\)-row direction with one \(\Gamma\)-direction. That mechanism is determinant geometry.

## Q3

**VERDICT: Gram–Schmidt gives legitimate nested scalar integrals, but not a clean iteration of SPEC, and it already assumes the missing determinant identity.**

For almost every \(A\), write \(q_i=A_iZ\) and
\[
P_i=Z\bigl(I-\Pi_{\operatorname{span}(q_1,\ldots,q_{i-1})}\bigr).
\]
Then
\[
q_i^\perp=A_iP_i
\]
and
\[
W_{\rm enn}(Z)
 =\int\prod_{i=1}^b
   \operatorname{frobSq}(A_iP_i)^{-a/2}\,dA.
\]
Tonelli permits row-by-row integration because the integrand is nonnegative. Each individual factor is algebraically a \(b=1\) Frobenius loss with
\[
m=1,\qquad c'=a/2.
\]

But it does not match SPEC as stated:

1. As an \(M_2\times n\) matrix, \(P_i\) has an \((i-1)\)-dimensional kernel. Hence its ordinary \(\operatorname{sigMin}\) is zero.

2. After quotienting out that kernel, the tail dimension is
   \[
   r_i=M_2-i+1.
   \]
   The quotient tail can retain several of the original \(j\) weak directions. There is no uniform reason that all but one of its nonzero singular values are bounded below. SPEC’s single-collapse hypothesis therefore fails without a further flag/sector decomposition.

3. The projected tail depends on all previous rows \(A_1,\ldots,A_{i-1}\). Applying SPEC to the innermost row produces a singular-value weight depending on those rows, not another determinant integral of the same form.

4. Removing one \(A\)-row leaves
   \[
   \det\operatorname{Gram}(q_1,\ldots,q_{b-1})^{-a/2}.
   \]
   The exponent remains \(a/2\). Thus even an ideal row iteration naturally gives a residual corner resembling \(a\times(b-1)\), not the required \((a-1)\times(b-1)\). It does not reproduce the charge \((a-1)(b-1)\).

For completeness, the full Gram–Schmidt/QR change of variables makes the hidden determinant explicit. Let
\[
H=ZZ^{\mathsf T}>0,\qquad B=AH^{1/2},
\qquad B^{\mathsf T}=UR,
\]
where \(U\) is Stiefel and \(R\) is upper triangular with \(r_{ii}>0\). Then
\[
dA=(\det H)^{-b/2}
 C_{d,b}\prod_{i=1}^b r_{ii}^{\,d-i}\,dR\,d\mu(U),
\]
while
\[
\det(AHA^{\mathsf T})=\prod_{i=1}^b r_{ii}^2.
\]
Thus the integrand times measure contains
\[
(\det H)^{-b/2}\prod_{i=1}^b r_{ii}^{d-i-a}.
\]
This recovers the criterion \(a<d-b+1\), but determinant geometry has merely migrated into \(\det H\), the residual norms, and the QR Jacobian. Moreover, the original box becomes an \(H\)-dependent, non-product QR region.

A conditional orthogonal split of a single row can have Jacobian \(1\), but that is not a global factorising change of variables; the domains and quotient tails remain coupled.

## Q4

**VERDICT: The proposed SPEC + PSD-only route does not close. A determinant factorisation is irreducible.**

What is derived exactly:

- Full determinant loss is strictly more singular than Frobenius-trace loss for \(b>1\).
- PSD projection leaves the exact threshold \(a<M_2-b-j+1\), not the designed threshold.
- In the complementary range, uniform boundedness of \(W_{\rm enn}\) is actually false.
- Row-wise scalarisation preserves exponent \(a\), does not shrink both corner dimensions, and produces quotient tails that need not satisfy SPEC’s single-collapse hypothesis.

What I infer structurally:

- No sequence of the two banked operations can manufacture the transition
  \[
  (a,b,M_2)\mapsto(a-1,b-1,M_2-1).
  \]
  Any lemma that does so must encode a Gram-volume pivot, even if presented as a change of variables or scalar peel.

The minimal identity to build is the one-step bordered-Gram/Schur-complement identity
\[
\boxed{
\det\operatorname{Gram}(q_1,\ldots,q_i)
 =
\det\operatorname{Gram}(q_1,\ldots,q_{i-1})
 \,\operatorname{dist}\!\left(
 q_i,\operatorname{span}(q_1,\ldots,q_{i-1})
 \right)^2
}
\]
on the independent locus, followed by induction. This is strictly smaller than full Cauchy–Binet: it applies only to successive Gram extensions and requires no sum over all \(b\times b\) minors. It is nevertheless genuinely a \(b\times b\) determinant identity. It supplies the missing algebraic bridge; additional measurable flag/sector and Jacobian bookkeeping will still be needed for the shell reduction.

Confidence: **98%**.

The computation that would flip my verdict is a uniform one-weak-direction lemma, proved solely from SPEC and PSD monotonicity, of the schematic form
\[
I_{a,b}(H_s+\tau^2uu^{\mathsf T})
 \le C\,\tau^{-\alpha}\,
 I_{a-1,b-1}(\widehat H_s),
\]
with the required tube-admissible \(\alpha\), uniform eigenspace constants, and no Schur complement, minor, QR, or equivalent volume identity. Such a lemma would iterate to the desired shrink. The trace-versus-determinant counterexample strongly indicates that any valid proof of it would contain the missing determinant identity in disguise.