### Q1

**VERDICT: SOUND-WITH-CAVEAT — null-set rationale and \(C_0\) terminology.**

On \(D(A)=\det(Q_bQ_b^\top)>0\), ATOM gives
\[
F(A)\le C_{\rm resid}D(A)^{-a/2}w^{-(c'-ab/2)}.
\]
Since \(Z^\top\) is injective with minimum stretch \(c_0\),
\[
D(A)\ge c_0^{2b}\det(AA^\top),
\]
so the determinant majorant is integrable when \(a<M_2-b+1\). The rank-drop set is null, hence contributes zero.

Correction: null-set deletion does not require \(w\) fixed or \(F(A)<\infty\); any nonnegative function integrates to zero on a null set. What matters is that the determinant majorant controls every shrinking neighborhood of that set.

Also, \(ab\) is the level-0 **freed contribution**, while the design’s total
\[
C_0=ab+R_t=\minAdm(M).
\]
Thus U3’s exponent shift is exact, but \(ab\neq C_0\) literally.

There is no conflict with the \(\sigma_{\min}\)-undershoot: that criticism concerns replacing the full product of singular values by a smallest-singular-value weight. The determinant retains the missing anisotropy.

### Q2

As literally stated, false if degenerate cuts with \(a=0\) count. Example:
\[
M=(1,5,1),\qquad t=1,
\]
is binding since its value is \(1<5\), but \(a=0,b=4,M_2=1\), so
\[
0\nleq 1-4+1.
\]

For every **nontrivial** binding cut \(a\ge1\), it is a theorem. Since \(t+1\) is admissible,
\[
ab+R_t\le(a-1)(b-1)+R_{t+1},
\]
hence
\[
R_{t+1}-R_t\ge a+b-1.
\]
The recursion for \(R\), reusing an optimizer for \(R_t\), gives
\[
R_{t+1}-R_t\le M_2.
\]
Therefore \(a+b-1\le M_2\), equivalently \(a\le M_2-b+1\). Add \(a>0\) explicitly; handle \(a=0\) separately.

### Q3

1. **R-CoV**, preferably using the CFC square root rather than LDL. The worktree already has `exists_gram_normalizer`, `rightMulₚ`, `det_rightMulₚ`, and `lintegral_comp_rightMulₚ`; Mathlib v4.29 supplies Haar scaling for invertible linear maps. **Biggest risk:** restricted-domain CoV plus enclosing the transformed parallelepiped in a bounded box/ball. The factorization and Jacobian are already banked.

2. **R-mono.** Mathematically shorter, but source inspection confirms v4.29 has PSD determinant nonnegativity, not Löwner determinant monotonicity. Building monotonicity through \(A^{-1/2}BA^{-1/2}\) and spectral arguments is substantially more API-heavy.

`LDL.lower_conj_diag` exists, but LDL does not expose a ready \(LL^\top\) Cholesky factor or diagonal-positivity package. `[v4.29 source-checked]`

A third route is to generalize the existing row-recursive `qbox_lintegral_lt_top` proof directly to ellipsoidal row domains. It avoids determinant monotonicity but duplicates projection and measure bookkeeping; I would not choose it.

### Q4

Mathlib lacks the packaged polynomial-null theorem, but this repository already supplies it: `MvPolynomial.volume_zeroSet_eq_zero` and `ae_eval_ne_zero`. It also has the matrix-shaped `ae_matrix_eval_ne_zero` and, most directly, `corank_survival_ae`. `[worktree source-checked]`

Recommended route:

1. Derive `rank Z = M₂` from `hZ`.
2. Apply `corank_survival_ae Z` to obtain `rank (A·Z)=b` almost everywhere.
3. Convert full row rank to Gram PosDef using the banked `posDef_gram_of_rank_eq`.

For the literal \(AA^\top\) statement, specialize to \(Z=I\).

A finite pointwise bound at singular \(A\) preserving the full \(ab/2\) shift is unavailable: the bounded brick instead costs \(w^{-c'}\). An extended RHS equal to \(\infty\) on the singular set is pointwise valid, but proving its integral finite still requires nullity.

### Q5

**VERDICT: SOUND-WITH-CAVEAT — fixed-coercive-sector scope.**

Land Obl-2 as the convergent, uniformly coercive-tail, atom-branch lemma:
\[
a<M_2-b+1,\qquad c'>ab/2.
\]
No multi-level flag is mathematically needed there.

Do not present it as the complete global off-sector descent: when \(Z\) varies and its coercivity constant degenerates, the determinant constant is nonuniform and tail stratification remains necessary.

The borderline may also admit a cheaper follow-up than a flag. Interpolating ATOM and BOUNDED with \(0<\theta<1\) yields
\[
D^{-\theta a/2}\,w^{-(c'-\theta ab/2)}.
\]
At \(a=M_2-b+1\), choose \(\theta<1\) so \(\theta a\) is integrable and, using the strict carrier margin, \(c'-\theta ab/2<R_t/2\). Thus tracking the borderline separately is sound; the \((3,3,3)\) undershoot does not force flags in the strict convergent regime.