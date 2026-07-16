**Q1.** Yes. Multi-scale singular values can beat the single-scale radial value, bottoming out at
\[
\operatorname{minAdm}(u,m,n)
=\min_{0\le t\le \min(u,m)}
\bigl[(u-t)(m-t)+tn\bigr].
\]
(The minimum is over integer \(t\).)

**Q2.** If layer \(i\), with \(d_i=M_{i-1}M_i\) parameters, scales as \(t^{c_i}\), then
\[
\operatorname{codim}_{\rm eff}
=\frac{\sum_i c_i d_i}{\sum_i c_i}.
\]
This is a weighted average, hence
\[
\operatorname{codim}_{\rm eff}\ge \min_i d_i\ge\operatorname{minAdm}(M_0,\ldots,M_L).
\]
Thus cross-layer scale differences do not undercut \(\minAdm\).

**Q3 — VERDICT: NO.** Indeed, choosing \(t=u\) in the recursion gives
\[
\minAdm(M_0,M_1,\mathrm{deep})
\le ab+\minAdm(u,\mathrm{deep}),
\]
so
\[
\minAdm(u,\mathrm{deep})\ge
\minAdm(M_0,M_1,\mathrm{deep})-ab.
\]