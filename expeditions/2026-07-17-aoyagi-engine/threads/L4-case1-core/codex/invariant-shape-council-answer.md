## 1. Q1 — recoord direction

**CONFIRMED:** use \(A_{S+1}Q_1\), with the \(-\gamma\) effect.

- **FACT:** Aoyagi defines the new coordinate by \(A'=R^{-1}A\).
- **INFERENCE:** A chart substitution uses the reverse map \(A=RA'\). Reversing/transposing the product changes left multiplication into right multiplication:
  \[
  A=RA' \quad\longmapsto\quad \widetilde A=\widetilde A'\widetilde R.
  \]
  With \(\widetilde R=Q_1\), this is \(A_{S+1}Q_1\). It places the clearing matrix next to the uncleared base factor and cancels the cross-term. \(Q_1^{-1}\) has the opposite sign and therefore doubles it.

Reversal alone does not invert \(Q_1\); the apparent inverse change comes from converting Aoyagi’s old-to-new coordinate formula into the new-to-old chart substitution.

## 2. Q2 — invariant shape

**Reading B is faithful.**

- **FACT:** The invariant is explicitly
  \[
  \operatorname{diag}(b)\begin{pmatrix}E_J&0\\0&D_J\end{pmatrix}\cdots .
  \]
  Thus the exceptional monomials belong to the external row-weight ledger, not internally to \(D_J\).
- **FACT:** In Case 1(1), \(d=u_{s,k}d'\) is the blow-up-chart substitution. Updating \(\widetilde t_{s,k}\) and \(M_{s,k}\) absorbs that new exceptional factor into the \(b\)-chain before the same invariant is carried onward. Hence it is transient factoring, not a permanent divisibility condition on the normalized residual \(D_J\).

The whole presented product does have \(b\)-scaled rows; “clean” applies specifically to the separated residual block. On that distinction, the text is not genuinely ambiguous.

**INFERENCE:** boost-readiness follows directly from the separated normal form: partial-block rows contribute a center coordinate from clean \(D_J\), while complementary rows acquire the reused exceptional coordinate from their external \(b_i\). No separate hypothesis that extra-block coefficients inside \(D_J\) factor by the exceptional is needed; the necessary factor is already recorded in the \(b\)-ledger.