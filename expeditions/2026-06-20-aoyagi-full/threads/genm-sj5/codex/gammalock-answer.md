The reconciliation is conditionally sound, but the proposed ADD explanation is false. Route A closes only because both separated factors independently tolerate the full target exponent.

### Q1 — REFUTE [DERIVED]

The claimed identities are false. Let

\[
B=\begin{bmatrix}q_1\\q_2\end{bmatrix}.
\]

For fixed \(s\),

\[
H_1(s)=\|q_1+s q_2\|=\|(1,s)B\|.
\]

Hence

\[
\sigma_{\min}(B)\sqrt{1+s^2}\le H_1(s),
\]

but generally \(H_1(s)\ne\sigma_{\min}(B)\). Moreover,

\[
\inf_{s\in\mathbb R}\|q_1+s q_2\|
=\operatorname{dist}(q_1,\operatorname{span}(q_2)),
\]

whereas

\[
\sigma_{\min}(B)
=\inf_{a^2+b^2=1}\|a q_1+b q_2\|.
\]

For example, \(q_1=(2,0)\), \(q_2=(0,1)\) gives \(\inf_s\|q_1+s q_2\|=2\), but \(\sigma_{\min}(B)=1\). Equality with \(\sigma_{\min}\) requires normalizing \((1,s)\) and including the missing projective direction.

Nevertheless, the important conclusion is confirmed: the component coercivity clause is unsatisfiable. Since \(\Gamma\) is free, \(\Gamma=0\) gives \(H_1=0\). Even if that point were deleted, \(\Gamma=t\Gamma_0\) gives

\[
H_1(t\Gamma_0)=|t|H_1(\Gamma_0)\longrightarrow0.
\]

The bound \(ZZ^\top\succeq\varepsilon^2I\) only yields

\[
\sigma_{\min}(\Gamma Z)\ge\varepsilon\,\sigma_{\min}(\Gamma),
\]

which cannot control a free \(\Gamma\).

Thus `residualCoercive D i₀` is not merely difficult to preserve: it is incompatible with a genuine free-\(\Gamma\) leaf.

### Q2 — GAP as stated [DERIVED]

Write

\[
T_u:=\inf_{\ell:k_\ell>0}
\frac{\operatorname{jac}_\ell+1}{2k_\ell},
\qquad D_\Gamma:=\dim\Gamma=bM_2.
\]

Assuming the uniform lower comparison

\[
\operatorname{decLoss}\gtrsim
\operatorname{commonDivisor}(u)^2\|\Gamma Z\|_F^2
\]

and \(ZZ^\top\succeq\varepsilon^2I\), Route A gives a separated majorant. Its two factors satisfy

\[
\int_0^1u_\ell^{\operatorname{jac}_\ell-2c'k_\ell}\,du_\ell<\infty
\iff
c'<\frac{\operatorname{jac}_\ell+1}{2k_\ell},
\]

and, by polar coordinates,

\[
\int_{\Gamma\text{-box}}\|\Gamma\|_F^{-2c'}\,d\Gamma<\infty
\iff c'<\frac{D_\Gamma}{2}.
\]

Therefore the Route-A threshold is exactly

\[
\boxed{\min\left(T_u,\frac{D_\Gamma}{2}\right)}.
\]

The charges do not add. A condition such as “\(u\)-charge plus \(\Gamma\)-dimension equals \(\minAdm\)” is useless for this product singularity. To reach \(C/2\), where \(C=\minAdm\), one needs simultaneously

\[
T_u\ge\frac C2,
\qquad
D_\Gamma\ge C.
\]

There is no condition of the form “the \(u\)-factor carries \(C-D_\Gamma\)”.

For the canonical width-two leaf \(M=(b,M_2)\),

\[
C=\minAdm(M)=bM_2=D_\Gamma.
\]

Thus Route A does close if the existing β-clause

\[
T_u\ge \frac12\minAdm(M)
\]

is retained. It closes by MIN with both entries at least the target, not by ADD. Without β—or without the identification \(D_\Gamma=\minAdm(M)\)—the stated assumptions do not establish the desired threshold.

### Q3 — CONFIRM, with a scope condition [DERIVED/INFERRED]

[DERIVED] The correct analytic γ-clause is the block condition

\[
ZZ^\top\succeq cI,\qquad c>0.
\]

Indeed,

\[
\|\Gamma Z\|_F^2
=\operatorname{tr}(\Gamma ZZ^\top\Gamma^\top)
\ge c\|\Gamma\|_F^2.
\]

This condition concerns only \(Z\), so the free integration and possible rank deficiency of \(\Gamma\) do not break it.

[INFERRED] It is preserved on a peel branch only when the “units sector” quantitatively controls the entire tail product \(Z\), uniformly over that branch. If \(A_2\) denotes merely one factor of

\[
Z=A_2A_3\cdots A_L,
\]

then \(\sigma_{\min}(A_2)\ge\varepsilon\) alone is insufficient: take \(A_2=I\) and \(A_3=0\). The sector must impose \(\sigma_{\min}(Z)\ge\varepsilon\), or provide an independently proved implication to it. The small-\(\sigma_{\min}(Z)\) complement must remain in recursive rank-drop branches.

### Final verdict

Drop the \(i_0\)-component γ: confirmed; it is unsatisfiable for a free \(\Gamma\).

Use Route A with block-level \(ZZ^\top\succeq cI\): sound on the quantitative units branch, provided:

1. β is retained: \(T_u\ge\frac12\minAdm\);
2. the leaf identity \(\dim\Gamma=\minAdm\) is established;
3. the uniform block lower comparison for `decLoss` is proved;
4. the units sector controls the whole \(Z\), with its rank-drop complement covered recursively.

With those conditions, the reconciliation is sound—but its threshold mechanism is MIN-of-two-full-budgets, not ADD.