### Q1 — PROVEN: bound the full residual \(R\)

For \(\mathrm{loss}=(wy)^2R\), an RLCT lower bound uses
\[
\mathrm{loss}\ge c(wy)^2,
\]
so \(R\ge c>0\) is the required condition. Bounding \(|1+pd|\) below is merely a sufficient certificate, since \(R\ge(1+pd)^2\); it is not necessary. On a compact domain where \(R>0\), continuity gives \(0<c\le R\le C\), making \(R\) a unit. Chart integrals are summed, but their convergence thresholds combine by a minimum, not by summing per-chart RLCTs.

### Q2 — PROVEN: the divisor read-off remains valid

At every point with \(R>0\), continuity supplies a neighbourhood on which \(R\ge c>0\). Thus the loss is locally equivalent to \((wy)^2\), regardless of whether \(1+pd\) vanishes. If \(wy\ne0\), the loss itself is positive and the point is loss-regular. If \(wy=0\), the only vanishing comes from the \(w,y\) divisors. There need not be one uniform \(c\) on the entire punctured tube if it approaches \(\{R=0\}\).

### Q3 — PROVEN: the same chart handles the exceptional corner

At a point with \(1+pd=0\), \(wy=0\), and \(R>0\), the same canonical chart has
\[
\langle\mathrm{loss}\rangle=\langle(wy)^2\rangle
\]
in the local real-analytic ring because \(1/R\) is regular there. The pivot-based proof of the identity fails, but the identity itself does not. No sibling pivot is required for this local RLCT calculation. Only corners accumulating on \(R=0\) require further treatment.

### Q4 — INFERENCE: it is the same recursion, but it must actually be performed

The identity \(\{R=0\}=\{\bar C^3\bar C^4=0\}\) identifies the unresolved stratum as another matrix-product-vanishing problem, so structurally this is option (a): recursion one level down. Codimension \(4\) alone does not make it harmless—integrability can be controlled by arbitrarily small tubes around a null set. The deeper charts must cover those tubes and verify that no new divisor has a smaller ratio. The present-level fan only needs to handle the complement and route the deep stratum into that recursion.

### Q5 — NOT PROVEN as stated; no pivot-induced hole follows

The sibling quotient formulas were not supplied, so one cannot prove that their exact common-zero locus is contained in \(\{R=0\}\). Moreover, for fixed \(\varepsilon>0\), a nonempty common tube
\[
\bigcap_j\{|q_j|<\varepsilon\}
\]
is open and hence positive-measure; it cannot literally be contained in a codimension-\(4\) set. But this does not make it an uncovered region: wherever \(R>0\), the canonical factorization already gives the required monomial estimate even when every pivot quotient is small. Near the displayed chart origin the canonical quotient is \(1\), so sufficiently small such tubes are empty there.

**Final verdict:** this is a **DETAIL-AT-SCALE obligation**: use the canonical chart wherever \(R>0\), and let deeper recursive charts resolve neighbourhoods of \(\{R=0\}\). The supplied facts show no **MONUMENT-ADJACENT positive-measure hole** caused by the codimension-\(1\) pivot hypersurface. The remaining unproved items are the sibling common-zero algebra and the recursive divisor-ratio bound.