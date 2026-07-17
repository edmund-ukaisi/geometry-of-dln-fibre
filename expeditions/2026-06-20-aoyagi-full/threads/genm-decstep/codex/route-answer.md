**Q1 — PROVEN gap in ROUTE-D as stated.** At a smooth rank-\(r\) point of an \(m\times q\) determinantal variety, the normal dimension is \(d=(m-r)(q-r)\); an ambient blow-up has
\[
|\det D\pi|=|e|^{d-1}\times\text{unit},
\]
and successive rank blow-ups similarly give nonnegative exceptional powers. This Jacobian is bounded above but vanishes, so its power must not be discarded. Crucially, resolving \(K\)’s determinantal ideal does not resolve the full loss ideal. Locally,
\[
Q_b\sim\operatorname{diag}(I_r,S),\qquad
\|\Gamma Q_b\|^2\sim\|\Gamma_1\|^2+\|\Gamma_2S\|^2,
\]
leaving the joint incidence \(\Gamma_2S=0\). Thus the pulled-back loss is not yet monomial-times-unit. Only a log resolution of the full joint ideal gives
\[
L\circ\pi=\Bigl(\prod |e_i|^{2N_i}\Bigr)u,\qquad
|\det D\pi|=\Bigl(\prod |e_i|^{a_i}\Bigr)v,
\]
with \(u,v\) positive units, hence net powers \(a_i-2cN_i\), which can be negative. The exact budgets \(1/2+5/2=3\) and \(2+7/2=11/2\) are correct arithmetic, but do not prove the claimed plain-chain reduction. ROUTE-DEC is sound only when its decorated hypothesis includes every rank/kernel stratum.

**Q2 — PROVEN.** There is no order-of-operations escape. Integrating \(\Gamma\) pushes Lebesgue measure through \(\Gamma\mapsto\Gamma Q_b\), whose coarea factor is
\[
\det(Q_bQ_b^\top)^{-a/2}.
\]
Resolving first instead produces positive Jacobian powers, but \(L^{-c}\) supplies the opposing negative exceptional powers. A complete joint resolution may hide the Gram weight, but it must account for exactly the same valuations. The failure \(\rho\notin L^4\) disproves the Hölder shortcut, not total integrability.

**Q3 — PROVEN insufficiency; INFERENCE on organization.** Plain RMBTF alone does not close the stated peel because it contains no information about the residual joint exceptional powers. Explicit decoration is not philosophically mandatory, but avoiding it requires proving an equivalent, stronger per-peel theorem: a uniform relative resolution of \((Q_{\!p},\Gamma Q_b)\), including all factorization and kernel-incidence strata, whose pushforward is a finite sum of shifted plain reduced-chain integrals. Standard determinantal Jacobian positivity does not supply that theorem; it effectively packages the decorated machinery into one analytic atom.

**Q4 — INFERENCE on the simpler proof architecture.** ROUTE-DEC, formulated with a full determinantal/flag-decorated induction, is the sounder organization because it exposes the weights that must be checked. ROUTE-D could become equally sound after proving the relative joint-principalization/pushforward atom above, but the proposed blow-up of \(K\) alone has a genuine gap and does not establish “fresh tail, no weight.”

**DECORATION-NECESSARY** (unless replaced by an equivalent relative joint-resolution atom).