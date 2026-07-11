Verdict: the proposed peel is not well-posed with the plain scalar box IH. The determinant is a genuine residual weight. This identifies a gap in the proof method, not a divergence of the true integral.

### Q1 — Is the determinant absorbed?

No.

**FACT.** Put \(G=Q_bQ_b^{\mathsf T}\). At full row rank, write
\[
Q_b=G^{1/2}V,\qquad VV^{\mathsf T}=I_b.
\]
For each row \(\gamma\in\mathbb R^b\),
\[
\gamma\longmapsto\gamma Q_b=(\gamma G^{1/2})V
\]
is an injection onto the \(b\)-dimensional row space of \(Q_b\). Its induced-volume Jacobian is
\[
\det(G)^{1/2}.
\]
For \(a\) rows,
\[
d\Gamma=\det(G)^{-a/2}\,dY.
\]
Thus \(\det(G)^{-a/2}\) really is the \(\Gamma\)-change-of-variables Jacobian—but it remains after that integration. When \(q>b\), the map is not a bijection onto \(\mathbb R^{a\times q}\); \(\Pi\) records its \(ab\)-dimensional image. Even when \(q=b\), the determinant still remains.

The scaling test is decisive. Fix \(Q_p=\widetilde Q_p=Z\neq0\), take \(B_{12}=0\), and let
\[
Q_b=\varepsilon R,\qquad \operatorname{rank}R=b.
\]
Then \(\Pi\) and the bracketed loss remain fixed, while
\[
\det(Q_bQ_b^{\mathsf T})^{-a/2}
=\varepsilon^{-ab}\det(RR^{\mathsf T})^{-a/2}\to\infty.
\]
The reduced-chain integrand, depending on \(Z\), stays fixed. Hence there is neither a uniform domination by nor an equality with the plain reduced-chain integrand.

**INFERENCE.** The determinant is an extra weight not present in the plain IH. A triangular change \(Q_p\mapsto\widetilde Q_p=Q_p+P^{-1}B_{12}Q_b\) has unit Jacobian and cannot cancel it.

For a bounded \(\Gamma\)-box, the full-space atom is an upper majorant. Failure of this majorant to be integrable does not imply failure of the true bounded-box integral.

### Q2 — Is “full rank a.e.” sufficient?

No. It is sufficient to apply the atom identity almost everywhere, but not sufficient to prove finiteness of the resulting outer integral.

**FACT.** Null-set values themselves are harmless by Tonelli. The problem is the neighborhood of the null set:
\[
\det(Q_bQ_b^{\mathsf T})^{-a/2}\to\infty .
\]
A function can be finite almost everywhere and still be nonintegrable; \(u\mapsto |u|^{-1}\) is the elementary model.

At an actual rank-deficient point, the full-space \(\Gamma\)-atom is typically infinite because directions in \(\ker(\Gamma\mapsto\Gamma Q_b)\) have infinite volume. The bounded-box inner integral may nevertheless remain finite when \(w>0\). Again, this separates failure of the atom majorant from behavior of the true integral.

**INFERENCE.** An \(A_2\)-rank-drop cannot be absorbed by the plain red-chain IH. The exact rank-drop locus need not be integrated separately—it is null—but its surrounding tube must be resolved. One needs either:

- a higher-rank-drop/\(M\)-value stratum analysis, or
- a strengthened anisotropic IH retaining the determinant/minor weight, or
- a uniformly truncated atom whose estimate saturates as \(Q_b\) degenerates.

The possible “min-caricature” collapse occurs when the determinant valuation and the reduced loss, which share the same deeper rank-drop divisor, are treated as independent scalar branches. Correct resolution adds their Jacobian charges along that shared divisor; an incorrect scalar split replaces this coupled addition by a minimum. Conversely, simply dropping the determinant overclaims finiteness.

### Q3 — Is \(c'=ab/2\) always strictly interior?

No. The stated inequality does not imply that.

**FACT.** From
\[
m:=\minAdm(M)\le ab+r,\qquad r:=\minAdm(\operatorname{redChain}_tM)\ge1,
\]
we know only that the particular candidate \(ab+r\) exceeds \(ab\). We do not know that the minimum \(m\) exceeds \(ab\).

There are three possibilities:

\[
\begin{array}{c|c}
ab<m & ab/2\text{ is strictly interior}\\
ab=m & ab/2=m/2\text{ coincides with the final threshold}\\
ab>m & ab/2\text{ lies above the admissible range.}
\end{array}
\]

For example,
\[
M=(4,4,2,2),\qquad t=2
\]
has
\[
ab=(4-2)^2=4,\quad \minAdm(M)=4,\quad
\minAdm(2,2,2)=3.
\]
Thus \(ab/2=\minAdm(M)/2=2\). The final theorem’s strict inequality excludes the endpoint, but it is not strictly interior.

If the chosen \(t\) actually realizes
\[
m=ab+r,
\]
then \(r\ge1\) does imply \(m>ab\), so the switch is interior on that minimizing branch. That stronger equality was not assumed.

**INFERENCE.** The combinatorial data allow the atom’s logarithmic borderline to coincide with the claimed final threshold. Actual logarithmic divergence of the true integral would require a matching local lower bound; it does not follow merely from the displayed inequality.

### Final adjudication

The peel step, as stated, is **not WELL-POSED with the plain box IH**. Its minimal missing result is joint weighted finiteness:
\[
\int
\det(Q_bQ_b^{\mathsf T})^{-a/2}
\,H(A',x)^{-(c'-ab/2)}
\,dA'\,dx<\infty,
\]
or an equivalent rank-stratified/truncated estimate. The scalar red-chain IH proves only the corresponding assertion without the determinant and therefore cannot close the atom-output majorant. An anisotropic carrier tracking the shared rank-drop divisor is required.