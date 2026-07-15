### Q1

- [FACT] \(d=M_2-b\).

- [FACT] With \(H=ZZ^{\mathsf T}>0\) and \(U=H^{-1/2}Z\), one has \(UU^{\mathsf T}=I_{M_2}\) and
  \[
  Q_b=(A_{\mathrm{cor}}H^{1/2})U,\qquad Q_p=(P_{\mathrm{pivot}}H^{1/2})U.
  \]

- [FACT] Thus both matrices lie in the \(M_2\)-dimensional space \(\operatorname{row}(Z)\); after removing \(\operatorname{row}(Q_b)\), the effective complement has dimension \(M_2-b\).

- [FACT] The remaining \(n-M_2\) directions lie in \(\operatorname{row}(Z)^\perp\), where \(Q_p\) and \(Q_b\) vanish identically, so they contribute no normal directions.

- [FACT] Consequently the incidence term is
  \[
  s(d-\ell)=s(M_2-b-\ell),
  \]
  not \(s(n-b-\ell)\).

### Q2

- [FACT] The answer is **polynomial-per-cell**, not nested-min-per-cell.

- [FACT] On the full-row-rank \(Z\)-chart,
  \[
  \operatorname{rank}(P_{\mathrm{pivot}}Z)=\operatorname{rank}(P_{\mathrm{pivot}}).
  \]
  Hence rank loss of \(Q_p\) is a condition on the deep variables, not on \((A_{\mathrm{cor}},\mathrm{front})\).

- [FACT] Its normal directions therefore belong to the separate deep comparator. If a front chart becomes nonuniform when those deep coefficients vanish, one refines it by deep cells; each resulting joint cell still has an integer-polynomial codimension.

- [FACT] A nested minimum appears only after minimizing over the family of deep cells, never inside one front normal-crossing cell.

### Q3

- [FACT] Assuming the stated identity,
  \[
  \min_{\ell,s}C_{\ell,s}
  =
  \min_{0\le s\le u}
  \bigl[(M_0-s)(M_1-s)+sM_2\bigr]-ab.
  \]
  Thus the front finiteness gate is governed by \(M_2\):
  \[
  K\le \min_{\ell,s}C_{\ell,s}.
  \]

- [FACT] This naive front minimum can be strictly larger than the true deep-chain minimum.

- [FACT] For example, with widths \((3,3,3,3)\), \(u=3\), and \(a=b=0\), the naive front value is
  \[
  \min_{0\le s\le3}\bigl[(3-s)^2+3s\bigr]=7,
  \]
  whereas resolving the deeper \(3\times3\times3\) comparator gives minimum \(6\).

- [FACT] The gap is carried by deeper comparator strata, not by replacing \(M_2\) with \(n\) or altering the front-cell codimension.