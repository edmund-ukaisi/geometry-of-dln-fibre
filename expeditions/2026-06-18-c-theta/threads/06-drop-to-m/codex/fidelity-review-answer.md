**Q1 index discipline**

**VALID.** Paper coordinate \(p\in\{1,\dots,N\}\) corresponds to Lean coordinate \(i=p-1\in\{0,\dots,N-1\}\).

Paper condition:
\[
p>m
\]
becomes
\[
i+1>m \iff i\ge m
\]
since \(i,m\) are integers. So the Lean wall \(e_i=0\) for 0-based \(i\ge m\) is the correct translation. The boundary Lean coordinate \(i=m\) is paper coordinate \(p=m+1\), hence it is indeed on the dropped side.

The target set is \(j<m\); the source set is \(k\ge m\). These are disjoint, so \(j\ne k\). The target set is nonempty because
\[
A_1=d_0+d_1-d_1=d_0\ge 0,
\]
so the maximising \(m\) satisfies \(m\ge 1\).

**Q2 integer gap**

**VALID.** Step (i) is an integer statement:
\[
m u_j\le \sum_{i<m}u_i
\]
because \(u_j\) is a minimum among exactly \(m\) terms, so each term is \(\ge u_j\), and summing gives \(\sum_{i<m}u_i\ge m u_j\). No division or rounding is involved.

The sum identity is consistent:
\[
\sum_{i<m}u_i
=
\sum_{i<m}e_i-md_0+\sum_{i<m}d_{i+1}
=
\sum_{i<m}e_i-md_0+(d_1+\cdots+d_m)
=
\sum_{i<m}e_i+(S-d_0)-md_0.
\]
Using \(\sum_{i<m}e_i\le d_0\), this gives
\[
m u_j\le S-md_0.
\]

For \(k\ge m\),
\[
k+1\ge m+1,
\]
so monotonicity gives \(d_{k+1}\ge d_{m+1}\). Thus
\[
u_k=e_k-d_0+d_{k+1}\ge 1-d_0+d_{m+1}.
\]
This uses the same \(d_{m+1}\) as the separation lemma; no hidden index mismatch.

Combining:
\[
m(u_k-u_j)
\ge m(1-d_0+d_{m+1})-(S-md_0)
= m+(m d_{m+1}-S)
\ge m+1.
\]

Step (vi) is valid integer reasoning. Let \(X=u_k-u_j\in\mathbb Z\). If \(X\le 1\), then since \(m\ge1\),
\[
mX\le m<m+1,
\]
contradicting \(mX\ge m+1\). Hence \(X\ge2\).

Then
\[
\Phi(e')-\Phi(e)=2(u_j-u_k+1)\le 2(-1)=-2<0.
\]

**Verdict:** the wall lemma \(e_i=0\) for 0-based \(i\ge m\) follows with no off-by-one and no division artefact.