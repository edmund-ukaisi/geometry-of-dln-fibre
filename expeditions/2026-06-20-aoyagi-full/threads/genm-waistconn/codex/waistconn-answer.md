**VERDICT:** **Scoped no-go for a direct single-mnp “LABOUR” reduction; every non-base waist shell nevertheless closes cleanly by transpose-reversal plus the ordinary one-shorter IH.**

### Q1–Q4

**Q1.** No single three-width chain records the deep charge in general.

Threshold-only candidates do cover:

\[
d(M)\le d(M_0,M_1,M_L) \quad\text{(F2)},
\]

and also

\[
d(M)\le d(M_0,M_1,M_2),
\]

because \(d(t,M_2,\ldots,M_L)\le tM_2\). But coverage is not domination.

Concrete obstruction:

\[
d(4,2,3,3)=\min\{8,\;3+d(1,3,3),\;d(2,3,3)\}
=\min\{8,6,5\}=5,
\]

whereas

\[
d(4,2,3)=\min\{8,6,6\}=6.
\]

Thus the flat three-width model misses one unit of deep charge.

Under reversal, a four-width chain uses the family

\[
(u,M_1,M_0).
\]

For longer chains there is no immediate three-width target: these are replaced by shorter chains \((u,M_{L-2},\ldots,M_0)\).

**Q2.** Use reversal and re-stratify; do not collapse \(Q\).

Let

\[
N=\operatorname{rev}M=(M_L,M_{L-1},\ldots,M_0).
\]

The coordinate change \(B_s=A_{L-1-s}^{\mathsf T}\) has Jacobian \(1\) and gives

\[
I(M,c')=I(N,c').
\]

The recurrence has the exact back-recursion, hence

\[
d(N)=d(M).
\]

Since \(M_1<M_i\) for every \(i\ge2\), when \(M\) has at least four widths,

\[
N_1=M_{L-1}>M_1\ge \min(N_2,\ldots,N_L).
\]

Thus \(N\) is not a strict front pinch. By the contrapositive of F1, **every reversed shell satisfies hpiv**.

For a reversed branch \(u\), put

\[
H_u=(M_L-u)(M_{L-1}-u),\qquad
D_u=d(u,M_{L-2},\ldots,M_0).
\]

Then

\[
d(M)=d(N)=\min_u(H_u+D_u),
\]

so

\[
c'<\frac{d(M)}2
\implies
c'-\frac{H_u}{2}<\frac{D_u}{2}.
\]

This is exactly the shifted IH threshold. The original waist shell need not map to a reversed shell: its integral is bounded by the whole reversed integral, which is then re-stratified.

Why collapse fails: a bounded-density replacement of \(Q\) by a free matrix would give

\[
I(4,2,3,3;c')\lesssim I(4,2,3;c'),
\]

contradicting divergence of the former for \(5/2<c'<3\) and finiteness of the latter. Moreover, on a partial-rank shell
\(\sigma_1(Q)\ge\varepsilon\), \(\sigma_2(Q)\to0\), the scalar tail IH sees only
\(\|Q\|_F\ge\varepsilon\); it carries no rank-defect charge.

**Q3.** Yes. The general route uses IH on every one-shorter reversed chain

\[
(u,M_{L-2},\ldots,M_0).
\]

The original tail IH \((M_1,\ldots,M_L)\) alone is insufficient for partial singular-value shells. A direct banked mnp reduction occurs only once the reversed reduction has three widths.

**Q4.** Reversal is essential to this clean route, though not logically unavoidable. It can be avoided when \(M_1=1\), when a relevant factor is uniformly nondegenerate, or with a stronger rank-stratified IH controlling small singular values rather than only \(\|Q\|_F\).

### Minimal checks

For \((2,1,2)\),

\[
d=\min\{2,2\}=2.
\]

It is already the mnp base; the threshold is \(c'<1\), and the target is \((2,1,2)\).

For \((2,1,2,2)\),

\[
d(1,2,2)=2,\qquad d(2,1,2,2)=\min\{2,2\}=2.
\]

The original \(u=1\) pivot fails since \(2>1\). Here \(M_1=1\), so exceptionally

\[
\|A_0Q\|_F=\|A_0\|_2\|Q\|_2,
\]

and the integral factors into the front Morse integral and the base integral for \((1,2,2)\), both finite for \(c'<1\).

The general route reverses to \((2,2,1,2)\). Its nontrivial base targets are

\[
(1,1,2),\quad d=1;\qquad (2,1,2),\quad d=2,
\]

with shifted inequalities

\[
c'-\tfrac12<\tfrac12,\qquad c'<1.
\]

### Most likely break

The formal route needs a non-circular proof of

\[
d(M)=d(\operatorname{rev}M)
\]

from the finite min-recursion. Transpose invariance of the integral alone does not transfer the required threshold.