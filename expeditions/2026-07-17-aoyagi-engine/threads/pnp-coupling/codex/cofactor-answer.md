**Q1.** For the actual core-derived residual, **yes**, provided we use the stronger termwise fact that every monomial contains exactly one layer-\((S+1)\) factor. A path monomial becomes
\[
u_{(S+1,k_{S+2},k_{S+1})}\,C_k(u)
\]
after \(qm\); only its layer-\(S\) factor is replaced by \(1\), \(d_{rc}\), or \(d_{rc}-d_{rJ}d_{Jc}\). Grouping by the displayed \(A_{S+1}\)-entry gives the required support decomposition, with coefficients ignoring layer \(S+1\). This does **not** follow from ordinary multi-affinity plus `Deg1SupportedSlot` alone: \(f(x,y)=x(1+y)\) is affine in both layers and supported on \(x\), but setting \(x=1\) gives \(1+y\), which is not supported on \(y\).

**Q2.** Under that core/cofactor hypothesis, **YES**: identity shear preserves both (a) and (b), so the Schur shear is not needed for Q1’s descent. It changes only layer \(S\), while the surviving \(A_{S+1}\)-factor supplies support. Canonical shear actually introduces
\[
-d_{rJ}d_{Jc}\,A_{S+1}[q,r]\cdots ,
\]
which has degree \(2\) only in layer \(S\) and degree \(1\) in layer \(S+1\). Since the child threshold is \(S+1\), that quadratic term is below the threshold and is allowed; there is no degree-\(2\) violation in any layer \(\ge S+1\).

**Q3.** Both mechanisms are needed, but for different pieces. Once the Schur-prepared form is available, the **b-chain combinatorics** gives the small-center decomposition: for \(i<J_1\),
\[
r_i(DH)_{ij}=\sum_k(r_iH_{kj})D_{ik},
\]
using partial-block coordinates and \(p\)-free coefficients; for \(i>J_1\), writing \(r_i=p\widetilde r_i\) gives
\[
r_i(DH)_{ij}=p\,[\widetilde r_i(DH)_{ij}],
\]
covering rows outside the partial block. The **shear** supplies the prepared/triangular form itself by clearing the \(\gamma\)-type cross-term that could involve neither \(p\) nor the partial block. Strictly, this requires \(p\) to occur exactly once in \(r_i\), and the stated \(i=J_1\) boundary must also be assigned to one side.

**Verdict:** Q1 descent and Q3 boost are distinct facts: cross-layer cofactor homogeneity proves Q1, whereas Q3 needs Schur preparation plus b-chain divisibility.