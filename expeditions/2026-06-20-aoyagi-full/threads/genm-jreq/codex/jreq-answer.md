VERDICT: DIFFERENT-SIMPLER-ARGUMENT

**Q1.** Let
\[
u=t+r=\min(M_0,M_1),\qquad a=M_0-u,\quad b=M_1-u.
\]
Then \(\min(a,b)=0\), so
\[
\frac12\operatorname{peelCharge}(M,u)=\frac{ab}{2}=0.
\]
Thus the comparator exponent is \(c'\). From \((*)\),
\[
\minAdm(M)\le 0+\minAdm(\redChain(u,M)),
\]
hence
\[
c'<\frac{\minAdm(M)}2
\le\frac{\minAdm(\redChain(u,M))}{2}.
\]
Therefore the strong IH applies at exponent \(c'\).

**Q2.** The corner \(D\in\mathbb R^{a\times b}\) is a singleton.

- If \(a=0\), the Gram exponent is \(a/2=0\), so the divisor is \(1\).
- If \(b=0\), then \(Q_{\mathrm{bot}}\) has zero rows, its Gram matrix is \(0\times0\), and
  \[
  \det(Q_{\mathrm{bot}}Q_{\mathrm{bot}}^T)=1.
  \]

In either case,
\[
\det(Q_{\mathrm{bot}}Q_{\mathrm{bot}}^T)^{-a/2}=1,
\qquad \frac{ab}{2}=0.
\]
The corner control is vacuous.

**Q3.** No. The determinant factor is identically \(1\), so it cannot degenerate as \(Z\) degenerates. The hard uniform Gram-divisor estimate used for \(j<r\) has nothing to control. Pivot localization and the head-coordinate change may remain, but the corner-integration argument is inert.

**Q4.** Peel at the maximal cut \(u=\min(M_0,M_1)\), collapse the first two layers to \(\redChain(u,M)\), and perform no \(D\)-integration. The Schur loss has no genuine corner term:

- if \(a=0\), the second summand
  \[
  \|C\widetilde Q+D Q_{\mathrm{bot}}\|_F^2
  \]
  is absent;
- if \(b=0\), \(D Q_{\mathrm{bot}}=0\), and the remaining nonnegative \(C\widetilde Q\) term may be discarded for domination.

After the bounded pivot/shear changes, the shell is bounded by
\[
C\cdot I_{\mathrm{comp},\,\redChain(u,M)}(c'),
\qquad C<\infty,
\]
with charge \(0\). The IH closes this because
\[
c'<\frac{\minAdm(M)}2
\le\frac{\minAdm(\redChain(u,M))}{2}.
\]
If \((*)\) is tight, the two thresholds are equal, and the original strict inequality still suffices.

**Most likely failure mode:** the formal head-split lemma may have been deliberately generalized to zero-dimensional blocks, with empty integration and empty determinants defined as \(1\). Then the same lemma can be invoked syntactically at \(j=r\), although its corner-control content specializes to exactly the vacuous argument above.