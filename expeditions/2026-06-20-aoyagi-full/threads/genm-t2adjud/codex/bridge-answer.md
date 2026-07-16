### Q1

No. F1–F3 are correct, given the stated properties of \(\Phi\). After change of variables,
\[
\mathrm{LHS}=\int_{\mathrm{Box}}\mathbf 1_{\{\mathrm{wec}(Q)=j\}}G(Q).
\]
Dropping the indicator yields \(\mathrm{LHS}\le\int_{\mathrm{Box}}G\), not an integral over \(\{\mathrm{wec}(Q)=0\}\). Obtaining the proposed RHS would require
\(\mathbf 1_{\{\mathrm{wec}=j\}}\le\mathbf 1_{\{\mathrm{wec}=0\}}\), which is false for \(j\ge1\). Tonelli and row splitting only reorder integrations; they cannot replace one disjoint domain by another.

### Q2

The inequality is false in general. A concrete counterexample is
\[
M_0=M_1=M_2=n=2,\quad Z=I_2,\quad r=2,\quad j=1,\quad 0<\varepsilon<1,
\]
with \(A\in[-1,1]^{2\times2}\) and \(c'=3/2\).

On PivotShell, \(\sigma_{\min}(A)\ge\varepsilon\), so the RHS is finite because \(3/2< M_0M_1/2=2\).

Near a smooth rank-one matrix, writing \(\delta=\sigma_{\min}(A)\), one has
\[
G(A)\gtrsim \delta^{-1}.
\]
The rank-one locus is locally a hypersurface, with \(\delta\) comparable to transverse distance. Consequently the shell integral contains \(\int_0^\eta\delta^{-1}\,d\delta=+\infty\). Thus LHS \(=+\infty\) while RHS is finite.

### Q3

Let \(d=M_0M_1\).

For \(\sigma_{\min}(Q)\ge\varepsilon\),
\[
G(Q)<\infty\quad\Longleftrightarrow\quad c'<\frac{M_0M_1}{2}.
\]
At equality there is logarithmic divergence; above it there is power divergence.

Suppose \(Q\) tends to a matrix of rank \(M_1-k\), with its remaining \(M_1-k\) singular values bounded away from zero. Then
\[
G(Q)\to+\infty
\quad\Longleftrightarrow\quad
c'\ge\frac{M_0(M_1-k)}2.
\]
Below this threshold \(G(Q)\) remains bounded and converges to the finite integral at the limiting matrix. These claims follow from local integrability transverse to a kernel of codimension \(M_0(M_1-k)\).

### Q4

The correct route requires an analytic degeneracy estimate, not domain reorganization. A deep-factor floor is the natural datum: if
\[
ZZ^\top\succeq\varepsilon'^2U_sU_s^\top,
\]
then
\[
WW^\top=A ZZ^\top A^\top
 \succeq\varepsilon'^2(AU_s)(AU_s)^\top.
\]
This retains \(m=M_1-j\) deep directions while allowing \(A\) to create the \(j\) weak directions. One must then stratify \(Z\), integrate the degeneracy of \(AU_s\), and prove the relevant integrability bounds. The floor alone is not the estimate, but it is the appropriate starting quantity; a floor on all of \(W\) describes Shell\(_0\) and cannot dominate Shell\(_j\).

**VERDICT:** not sound; correct route is deep-factor stratification plus analytic integrability estimates for the front degeneracy.