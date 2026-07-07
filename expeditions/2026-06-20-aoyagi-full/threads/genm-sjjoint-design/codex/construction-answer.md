**Status:** the clean induction is a **decorated joint-resolution induction**, not a black-box shorter-chain induction. It closes only after proving one new normal-form lemma for the Gram determinant and residual core together.

**Q1. Strengthened Object**

Use an inductive object indexed by a partial rank profile
\[
\pi=(t_1,\dots,t_k),\quad t_0=M_0,
\]
with accumulated charge
\[
A(\pi)=\sum_{j=1}^k (t_{j-1}-t_j)(M_j-t_j).
\]

The object is not just a shorter chain. It is a **decorated residual integral**
\[
I_\pi(s)=\int W_\pi\cdot F_\pi^{-s},
\]
where:

- \(F_\pi\) is the current Schur/projection residual core.
- \(W_\pi\) is the product of Gram determinant factors already created by previous peels.
- The datum carries a common exceptional-divisor support table: for each divisor, the order of every core generator, every Gram minor, and the Jacobian.

That last item is essential. It records **which variables are shared**. A threshold-only invariant cannot distinguish \(\langle \delta x,\delta y\rangle\) from \(\langle \delta_1x,\delta_2y\rangle\).

Define the remaining threshold by
\[
\Theta(M,\pi)=\frac12\left(\min_{T\succeq \pi} Mval_M(T)-A(\pi)\right).
\]

IH:

\[
I_\pi(s)<\infty \quad \text{for every } s<\Theta(M,\pi).
\]

Original Box is \(\pi=\varnothing\), \(A=0\), so \(\Theta=\frac12\minAdm(M)\).

Peeling at the next cut \(u=t_{k+1}\) adds
\[
a=(t_k-u)(M_{k+1}-u),
\]
creates the Gram factor, and shifts
\[
s\mapsto s-a/2.
\]
The child profile is \(\pi'=(\pi,u)\), and
\[
s<\Theta(M,\pi)\implies s-a/2<\Theta(M,\pi').
\]
So the induction is well-founded by finite rank-profile length, equivalently the Aoyagi-style \((S,J)\) progression through finitely many layers/blocks. Base case is the terminal one-matrix/free-vector endpoint, handled by ordinary polar coordinates or Schur rank charts.

**Q2. Binding Branch \(M=(3,3,3,3)\)**

Binding profile:
\[
T=(2,1,0).
\]

Charges:
\[
(3-2)(3-2)=1,\quad (2-1)(3-1)=2,\quad (1-0)(3-0)=3.
\]

Thus
\[
Mval(T)=1+2+3=6,\qquad \frac12Mval=3.
\]

Take
\[
c'=3-\varepsilon.
\]

First peel \(t_1=2\):

\[
a_1=1,\qquad s_1=c'-1/2=5/2-\varepsilon.
\]

The decorated child threshold is

\[
\frac12(6-1)=5/2,
\]
so \(s_1<5/2\). The Gram factor is not paid by spare Hölder slack; it is already in the child object’s divisor ledger.

Second peel \(t_2=1\):

\[
a_2=2,\qquad s_2=s_1-1=3/2-\varepsilon.
\]

The next threshold is

\[
\frac12(6-1-2)=3/2,
\]
so \(s_2<3/2\).

Base endpoint has charge \(3\), so the final polar condition is

\[
2s_2=3-2\varepsilon<3.
\]

Equivalently, along the full terminal branch:
\[
2c'=6-2\varepsilon<1+2+3=6.
\]

That is the recovered budget. The Gram pole is paid because its order is added on the **same resolved divisors** as the residual core, not split into an independent integrability demand.

**Q3. Hardest Brick**

The genuinely new brick is:

\[
\textbf{simultaneous monomialization of } 
\det(Q_bQ_b^T)
\textbf{ and the projected residual core.}
\]

Concretely, for \(Q_b=RZ\), one must prove a finite chart decomposition where

\[
Q_b=D_b\,U_b,\qquad U_bU_b^T \text{ uniformly nonsingular},
\]
so
\[
\det(Q_bQ_b^T)\asymp \prod_i b_i^2.
\]

Then
\[
\det(Q_bQ_b^T)^{-p/2}\asymp \prod_i |b_i|^{-p},
\]
whose total order is \(pq=a\).

The projection is controlled because the diagonal cancels:
\[
P_{Q_b}=U_b^T(U_bU_b^T)^{-1}U_b.
\]
So \(I-P_{Q_b}\) introduces no hidden \(b_i^{-1}\) poles. The same \(b_i\)’s remain visible in \(Q_p\), \(Q_b\), and the later residual generators. That is exactly how corank \(\ge2\) sharing closes: the divisor labels are shared, not duplicated.

A useful concrete identity is

\[
\det(Q_bQ_b^T)=\|\wedge^q Q_b\|^2.
\]

So the proof should principalize the vector of maximal minors of the product \(Q_b\), jointly with the residual-core generators. Sum-of-squares prevents cancellation once one transformed Plucker coordinate is a unit.

**Most Likely Formalization Stall**

The stall point is proving the joint normal form for a **matrix product**, not for a free matrix:

\[
Q_b=A_{k,b}\,A_{k+1}\cdots A_{L-1}.
\]

A free-matrix Schur chart is standard. The product case must preserve the shared deeper factors while resolving both the Gram minors and \(Q_p(I-P_{Q_b})\). If this normal-form/principalization lemma is admitted, the induction closes by monomial endpoint inequalities. Without it, the construction does not close cleanly.