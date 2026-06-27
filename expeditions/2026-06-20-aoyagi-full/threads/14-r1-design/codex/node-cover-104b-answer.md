codex
I’ll treat your verified formulas as inputs and focus on the analytic reading: first the product/Fubini threshold, then the Schur-core threshold and whether the cross term changes it.
codex
**Verdict**

Your threshold reading is sound:

\[
\operatorname{rlct}(F,0)=\min\{mk/2,\operatorname{rlct}(\mathrm{core})\}
=\frac12\min\{mk,n+R\}.
\]

The only correction is wording: the displayed single chart is not itself already a full normal-crossing resolution unless the child has been resolved recursively. But there is no hidden cap in `core`, and no gluing flaw that changes the value.

**FACT: Outer Product Step**

In the pivot chart,

\[
F\circ\phi=y_0^2 K(z),\qquad |\operatorname{Jac}\phi|=|y_0|^{mk-1},
\]

where \(K=\mathrm{core}\) depends only on \(z=(u,v,W,B)\), not on \(y_0\). Hence on a product neighborhood,

\[
\int |F\circ\phi|^{-c}|\operatorname{Jac}\phi|
=
\left(\int |y_0|^{mk-1-2c}\,dy_0\right)
\left(\int K(z)^{-c}\,dz\right).
\]

The \(y_0\)-integral is finite iff

\[
mk-1-2c>-1 \iff c<mk/2.
\]

So

\[
\operatorname{rlct}_{\text{chart}}(F)=
\min\{mk/2,\operatorname{rlct}(K)\}.
\]

Thus your outer MIN is correct.

**FACT: Cross Term Does Not Lower `core`**

After the Schur change of variables, write \(e=Erow\in\mathbb R^n\), \(C=SBred\in\mathbb R^{(m-1)\times n}\). Then

\[
K(e,v,S,B)=\|e\|^2+\|ve+C\|^2.
\]

For bounded \(v\), this is comparable to

\[
H(e,S,B)=\|e\|^2+\|SBred\|^2.
\]

Indeed,

\[
\|SBred\|\le \|ve+SBred\|+\|v e\|
\]

gives one inequality, and the reverse inequality is immediate from

\[
\|ve+SBred\|\le \|v e\|+\|SBred\|.
\]

So there are constants \(0<a<b<\infty\) locally such that

\[
aH\le K\le bH.
\]

Comparable nonnegative analytic germs have the same local integrability threshold. Equivalently, completing the square in each column shows the \(v_iE_j\) term only changes the positive definite metric.

Therefore the cross term introduces no product-type cap.

**INFERENCE: Inner Additivity**

Since \(H=\|e\|^2+\|SBred\|^2\) is a sum in disjoint variable groups, with \(u,v\) only passive bounded variables,

\[
\operatorname{rlct}(K)=\operatorname{rlct}(H)
=
\operatorname{rlct}(\|e\|^2)+\operatorname{rlct}(\|SBred\|^2).
\]

The first term is \(n/2\). The child term is \(R/2\). Hence

\[
\operatorname{rlct}(\mathrm{core})=\frac n2+\frac R2.
\]

No additional internal minimum appears at the `Erow` level.

**About The Chart / Resolution Claim**

As an RLCT computation, the two-strata reading is correct uniformly:

\[
\operatorname{rlct}(F,0)
=
\min\left\{ \frac{mk}{2},\frac{n+R}{2}\right\}.
\]

But literally, one pivot chart plus the displayed Schur split is not already a complete normal-crossing resolution unless the child singularity has also been resolved. The correct statement is recursive: after the first \(A\)-blowup, the \(y_0\) divisor gives the \(mk/2\) candidate, and the unit-pivot core reduces to \(n/2\) plus the child RLCT. Other pivot charts are equivalent by row/column permutations, so no residual lower stratum is missed.

**Checks**

For \((m,k,n)=(2,2,2)\):

\[
R=\min\{1,2\}=1,\qquad
\min\{mk,n+R\}=\min\{4,3\}=3.
\]

So

\[
\operatorname{rlct}=3/2.
\]

Core/child branch binds.

For \((2,2,4)\):

\[
R=\min\{1,4\}=1,\qquad
\min\{4,5\}=4.
\]

So

\[
\operatorname{rlct}=2.
\]

The \(y_0\) divisor binds.

For \((1,1,2)\):

\[
F=a^2(b_1^2+b_2^2).
\]

The product thresholds are \(1/2\) from \(a^2\) and \(1\) from \(b_1^2+b_2^2\), so

\[
\operatorname{rlct}=1/2.
\]

So: the MIN reading is sound; the inner `core` has no hidden cap; the only caveat is that “single chart is already a normal-crossing resolution” should be read as “single pivot chart plus recursive child resolution/additivity computes the threshold.”
tokens used
**Verdict**

Your threshold reading is sound:

\[
\operatorname{rlct}(F,0)=\min\{mk/2,\operatorname{rlct}(\mathrm{core})\}
=\frac12\min\{mk,n+R\}.
\]

The only correction is wording: the displayed single chart is not itself already a full normal-crossing resolution unless the child has been resolved recursively. But there is no hidden cap in `core`, and no gluing flaw that changes the value.

**FACT: Outer Product Step**

In the pivot chart,

\[
F\circ\phi=y_0^2 K(z),\qquad |\operatorname{Jac}\phi|=|y_0|^{mk-1},
\]

where \(K=\mathrm{core}\) depends only on \(z=(u,v,W,B)\), not on \(y_0\). Hence on a product neighborhood,

\[
\int |F\circ\phi|^{-c}|\operatorname{Jac}\phi|
=
\left(\int |y_0|^{mk-1-2c}\,dy_0\right)
\left(\int K(z)^{-c}\,dz\right).
\]

The \(y_0\)-integral is finite iff

\[
mk-1-2c>-1 \iff c<mk/2.
\]

So

\[
\operatorname{rlct}_{\text{chart}}(F)=
\min\{mk/2,\operatorname{rlct}(K)\}.
\]

Thus your outer MIN is correct.

**FACT: Cross Term Does Not Lower `core`**

After the Schur change of variables, write \(e=Erow\in\mathbb R^n\), \(C=SBred\in\mathbb R^{(m-1)\times n}\). Then

\[
K(e,v,S,B)=\|e\|^2+\|ve+C\|^2.
\]

For bounded \(v\), this is comparable to

\[
H(e,S,B)=\|e\|^2+\|SBred\|^2.
\]

Indeed,

\[
\|SBred\|\le \|ve+SBred\|+\|v e\|
\]

gives one inequality, and the reverse inequality is immediate from

\[
\|ve+SBred\|\le \|v e\|+\|SBred\|.
\]

So there are constants \(0<a<b<\infty\) locally such that

\[
aH\le K\le bH.
\]

Comparable nonnegative analytic germs have the same local integrability threshold. Equivalently, completing the square in each column shows the \(v_iE_j\) term only changes the positive definite metric.

Therefore the cross term introduces no product-type cap.

**INFERENCE: Inner Additivity**

Since \(H=\|e\|^2+\|SBred\|^2\) is a sum in disjoint variable groups, with \(u,v\) only passive bounded variables,

\[
\operatorname{rlct}(K)=\operatorname{rlct}(H)
=
\operatorname{rlct}(\|e\|^2)+\operatorname{rlct}(\|SBred\|^2).
\]

The first term is \(n/2\). The child term is \(R/2\). Hence

\[
\operatorname{rlct}(\mathrm{core})=\frac n2+\frac R2.
\]

No additional internal minimum appears at the `Erow` level.

**About The Chart / Resolution Claim**

As an RLCT computation, the two-strata reading is correct uniformly:

\[
\operatorname{rlct}(F,0)
=
\min\left\{ \frac{mk}{2},\frac{n+R}{2}\right\}.
\]

But literally, one pivot chart plus the displayed Schur split is not already a complete normal-crossing resolution unless the child singularity has also been resolved. The correct statement is recursive: after the first \(A\)-blowup, the \(y_0\) divisor gives the \(mk/2\) candidate, and the unit-pivot core reduces to \(n/2\) plus the child RLCT. Other pivot charts are equivalent by row/column permutations, so no residual lower stratum is missed.

**Checks**

For \((m,k,n)=(2,2,2)\):

\[
R=\min\{1,2\}=1,\qquad
\min\{mk,n+R\}=\min\{4,3\}=3.
\]

So

\[
\operatorname{rlct}=3/2.
\]

Core/child branch binds.

For \((2,2,4)\):

\[
R=\min\{1,4\}=1,\qquad
\min\{4,5\}=4.
\]

So

\[
\operatorname{rlct}=2.
\]

The \(y_0\) divisor binds.

For \((1,1,2)\):

\[
F=a^2(b_1^2+b_2^2).
\]

The product thresholds are \(1/2\) from \(a^2\) and \(1\) from \(b_1^2+b_2^2\), so

\[
\operatorname{rlct}=1/2.
\]

So: the MIN reading is sound; the inner `core` has no hidden cap; the only caveat is that “single chart is already a normal-crossing resolution” should be read as “single pivot chart plus recursive child resolution/additivity computes the threshold.”
