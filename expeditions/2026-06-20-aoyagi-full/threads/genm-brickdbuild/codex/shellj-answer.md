## 1. SOUNDNESS VERDICT

**TRUE**, for each fixed \(ab/2<c'<T_1\).

**OBSERVED FACT (derived using K1).** The shell-\(j\), `IsUnit P` domain is a subset of the off-shell domain, hence
\[
L_j(c')\le L_{\mathrm{off}}(c')<\infty .
\]
Writing \(q=c'-ab/2\), the cut \(u\) in the definition of \(T_1\) gives
\[
q<\tfrac12\minAdm(\operatorname{redChain}_uM),
\]
so the reduced comparator \(R_q\) is finite and positive. Therefore
\[
C_j:=L_j(c')/R_q<\infty
\]
proves \((\ast_{T1})\).

**OBSERVED FACT (verified corner).** The partial floor does not generally remove the binding corner. Take
\[
M=(2,2,3),\quad t^\*=0,\quad j=u=1,\quad a=b=1,
\]
so \(T_1=2\). Put \(Z=I_3\), \(Q_p=e_1\), and
\[
Q_b=(1,t_2,t_3).
\]
Then `hsQ` has one strong singular value and one weak singular value \(\asymp |t|\). With
\[
x=P+B,\qquad y=C+\Gamma,
\]
and \(B,\Gamma\) bounded away from zero,
\[
\mathrm{freedSchurLoss}
=x^2+y^2+(B^2+\Gamma^2)(t_2^2+t_3^2)
\asymp x^2+y^2+t_2^2+t_3^2.
\]
Here \(P=x-B\) remains invertible. Thus the local integral is
\[
\int_0^\delta r^{3-2c'}\,dr,
\]
which diverges at \(c'\ge2=T_1\). Hence \(\lambda_j=T_1\) in this example.

**INFERENCE.** The claim is true below \(T_1\), but not because the shell necessarily excludes the binding geometry. No strict threshold improvement can be asserted generally.

## 2. CHEAPEST SOUND ROUTE

The cheapest existential proof is K1 plus the ratio argument above, but that is unusable as a recursive proof.

The minimal non-circular analytic route is:

1. Apply a shell-localized K3 with
   \[
   w=\|[P\mid B_{12}]\,hsQ\|_F^2,\qquad C_{\rm cross}=CQ_p.
   \]
2. Prove the one genuinely new lemma below.
3. Integrate the resulting reduced comparator.

The missing lemma is the **partial-shell transverse-Schur estimate**. For \(q=c'-ab/2\),
\[
\begin{aligned}
&\int_z\int_{A\in S_j(z)}
 \det(Q_bQ_b^\top)^{-a/2}
 \int_{P,B,C}
 \Big(
   \|[P\mid B]hsQ\|_F^2+
   \|CQ_p(I-\Pi_b)\|_F^2
 \Big)^{-q}  \\
&\qquad\le K_{j,c'}\int_z
 \bigl(\operatorname{commonDivisor}(z)^2\|Q_p(z)\|_F^2\bigr)^{-q},
\qquad K_{j,c'}<\infty .
\end{aligned}
\]
This must include the incidence region
\(\operatorname{row}(Q_b)\to\operatorname{row}(Q_p)\); the residual may not be discarded.

K3’s coupled weight is therefore the correct algebraic starting point. K5 alone does not decouple it:
\[
w=r^2\|\widehat W\,hsQ(A_{\rm cor})\|_F^2
\]
still depends on \(A_{\rm cor}\). Consequently K4 cannot yet apply. Any additional “K5 decoupling” theorem strong enough to feed K4 is essentially the new lemma above in another form.

## 3. THE WALL

**Genuine WALL**, not routine bookkeeping.

The missing ingredient is a uniform shell-incidence estimate controlling the joint degeneration
\[
\det(Q_bQ_b^\top)^{-a/2}
\quad\text{and}\quad
Q_p(I-\Pi_b)
\]
as the two row spaces align, with exactly the reduced exponent \(c'-ab/2\).

K2 shows why bare determinant control is insufficient: in the example above,
\[
\det(Q_bQ_b^\top)\asymp1,
\qquad
\|Q_p(I-\Pi_b)\|^2\asymp |t|^2.
\]
K5/K6 handle radial and fixed-rank pieces, but not this moving-subspace incidence integral. The missing item is mathematics, not a specific Mathlib primitive.