1. **VERDICT: RATIONAL-RECOVERABLE** — by a rational coordinate-level SVD refinement, not by Cholesky recursion alone.

2. **Device: two-sided Cayley singular-frame chart.** For \((s,z)=(3,4)\), put
\[
C_n(X)=(I-X)(I+X)^{-1},\qquad E=(I_3\ 0),
\]
with \(K\in\mathfrak{so}(3)\), \(L\in\mathfrak{so}(4)\), and define
\[
A_0=B\,C_3(K)^\top,\qquad
A_1=C_3(K)\operatorname{diag}(t_1,t_2,t_3)E\,C_4(L).
\]
This is rational, and \(V_3(\mathbb R^4)\cong SO(4)\), so no abstract Stiefel measure occurs. With standard skew coordinates,
\[
|\det D\Phi|=
\frac{2^9\,t_1t_2t_3
 \prod_{i<j}|t_i^2-t_j^2|}
{\det(I+K)^2\det(I+L)^3}.
\]
The denominator is a positive rational unit on bounded Cayley charts. Moreover,
\[
\|A_0A_1\|_F^2=\sum_{j=1}^3 t_j^2\|B_{\bullet j}\|^2.
\]
Thus loss and amplitude are jointly monomialised.

For comparison, the generic repeated-eigenvalue locus in \(\mathrm{Sym}_3\) has
\[
\dim=2\text{ eigenvalues}+2\text{ orbit dimensions}=4,
\qquad \operatorname{codim}_{\mathbb R}=6-4=2.
\]
A local algebraic blow-up \((a,b)=(r,rv)\) contributes \(|r|^{2-1}=|r|\), comparable to one eigenvalue-gap factor. But the locus is singular along the scalar line, and this blow-up alone does not diagonalise \(\operatorname{tr}(MG)\). The Cayley chart does both.

3. **Worked \((4,3,4)\).** On \(t_1\ge t_2\ge t_3\ge0\),
\[
\prod_{i<j}|t_i^2-t_j^2|\le t_1^4t_2^2.
\]
Since \(z-s=1\), the resulting radial powers are
\[
h^{\rm rat}=(1,1,1)+(4,2,0)=(5,3,1).
\]
After the \(x=4\) ambient cap:
\[
\sum_j\min(4,h_j+1)=\min(4,6)+\min(4,4)+\min(4,2)=4+4+2=10.
\]
Hence \(c<10/2=5\). Route C had \(h^C=(3,2,1)\), charge \(4+3+2=9\); the new chart raises mode \(2\) from \(2\) to \(3\), exactly the missing power \(1\).

4. **Termination / atlas.** For the anchor, one spectral layer suffices. Shifted Cayley charts give a finite atlas: at most \(4\cdot8=32\) \(SO(3)\times SO(4)\) chart pairs, followed by a finite sign gauge. The omitted sets
\[
t_3=0,\qquad t_i=t_j,
\]
have Lebesgue measure zero and are benign. For fixed general \(s,z\), replace \(SO(4)\) by an iterated stereographic–Householder rational Stiefel chart; recursion depth is \(s\), with finitely many pole/sign charts.

5. **Sharpest possible failure.** The Gram-level Jacobian is insufficient unless the full same-dimensional \(A_1\)-chart is injective after sign gauging. Cheapest decisive test: symbolically factor the anchor’s explicit \(12\times12\) Jacobian and verify that its quotient by
\[
t_1t_2t_3\prod_{i<j}(t_i^2-t_j^2)
\]
is precisely the nonvanishing rational Cayley unit above.