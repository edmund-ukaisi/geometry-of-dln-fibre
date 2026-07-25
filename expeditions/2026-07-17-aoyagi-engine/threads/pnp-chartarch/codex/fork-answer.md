**Q1 — Yes: genuinely shear-after-blow-up.**  
The shear is load-bearing, not accidental. The pivot is
\[
\mathrm{peeled}_{00}=x_8+x_0x_{12}+x_1x_{16}.
\]
Under \(B\), this becomes \(u_0+u_8u_{12}+u_9u_{16}\), hence is not divisible by \(u_0\). Under \(H\circ B\), the replacement
\[
x_8=u_0-u_8u_{12}-u_9u_{16}
\]
cancels the other two terms exactly, leaving \(u_0\). The analogous cancellations in \(x_4,\ldots,x_7\) produce factors \(u_0u_1\). Since \(g_{\mathrm{Faithful}}=H\circ B\) extensionally, its monomialisation survives decomposition exactly; F3 merely shows that dropping \(H\) changes the map critically.

**Q2 — The determinant follows compositionally, with one odd permutation.**  
Write \(B=P\circ A_0\circ A_1\), where:

- \(A_1\) blows up pivot \(u_1\) with center \(\{1,5,6,7\}\), giving determinant \(u_1^3\);
- \(A_0\) then blows up pivot \(u_0\) with center \(\{0,\ldots,7\}\), giving determinant \(u_0^7\);
- \(P\) sends the first twelve output slots according to
  \[
  (8,9,10,11,1,5,6,7,0,2,3,4).
  \]

This permutation has \(45\) inversions, hence determinant \(-1\). Therefore
\[
\det DB=-u_0^7u_1^3,\qquad
\det D(H\circ B)=(1)(-u_0^7u_1^3).
\]
The relabeling is mathematically benign, but it must be represented explicitly (or absorbed by conjugating/reindexing the block maps). Raw block maps alone do not perform it.

**Q3 — No crux re-proof is required.**  
Prove the pointwise identity \(g_{\mathrm{Faithful}}=H\circ B\), then rewrite the already-proved divisibility and ideal identity along that equality. Independently derive the Jacobian from \(A_1,A_0,P,H\) and the chain rule. Jacobian bookkeeping does not reopen any statement about `peeled`.

**Q4 — Main trap: silently omitting the coordinate permutation.**  
Without the odd permutation—or with its order reversed—the composite is not extensionally \(g_{\mathrm{Faithful}}\), the determinant sign is wrong, and the banked crux cannot be transferred.

Confidence ranking: Q1 = Q3 > Q2 > Q4; all high.