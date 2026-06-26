<task>
Adjudicate whether an UPPER-BOUND (finiteness) atom for a deep-linear-network RLCT is PROVABLE from a
particular combinatorial resolution atlas, or whether it has a genuine obstruction. This is a
resolution-of-singularities COMPLETENESS question.

SETUP (exact). Widths M=(M_0,...,M_L), factors A^(s) of shape M_s x M_{s+1}, loss
F = ||A^(0)...A^(L-1)||_F^2 near A=0, flat dimension N = sum_s M_s M_{s+1}. We want the UPPER bound
on the RLCT: for c' < (1/2)minAdm(M), the integral INT_{(-1,1)^N} |F|^{-c'} dx < +infinity.

minAdm(M) = min over admissible exponent paths T=(t_1,...,t_L), t_0:=M_0, t_L:=0, weakly decreasing
(t_1 >= ... >= t_L=0, t_1<=min(M_0,M_1), t_j<=M_{j+1}), of
   Mval(M,T) = sum_{j} (t_{j-1}-t_j)(M_{j+1}-t_j).

THE ATLAS. There is a COMBINATORIAL leaf family {leaf i}: the leaves are the admissible descent paths
(pivot-branch choices). Each leaf carries monomial exponent data (d_i, k_i, h_i) where d_i is a chart
dimension and k_i, h_i : Fin(d_i) -> Nat are loss-base / Jacobian exponents, built by folding the
per-pivot codims along the path (a "foldDivisors" of the path's branch codims). The atlas is PROVEN to
satisfy: (threshold_ge) every leaf's monomialThreshold = inf_{k_ij != 0}(h_ij+1)/(2 k_ij) >= minAdm/2;
(achiever) some leaf realises = minAdm/2. So inf over leaves of monomialThreshold = minAdm/2 — the VALUE.

THE UPPER-BOUND ATOM (hfin). For all c':
   IF  sum_i INT_{[0,1]^{d_i}} (prod_j |y_j|^{h_ij}) (prod_j |y_j|^{k_ij})^{-2c'} dy  <  +infinity   (the
       leaf-sum of the MODEL monomial integrals is finite)
   THEN  INT_{(-1,1)^N} |F|^{-c'} dx  <  +infinity   (the ACTUAL loss integral is finite).
This is the upper bound rlctAtOn(F) >= minAdm/2: below the achiever threshold, the actual integral is
finite. The leaf-sum is finite exactly when every leaf threshold > c', i.e. c' < minAdm/2.

THE SUSPECTED OBSTRUCTION. The leaf (d,k,h) data is "threshold-only" — it records per-pivot
multiplicities (codims), NOT the SYMBOLIC coupling of which exceptional divisor multiplies which
generator. A prior exact computation found: for M=(3,3,4) (minAdm=8, the corank-2 binding case), the
threshold-only recursion computes codim 3 (so it would model rlct 3/2), but the TRUE rlct is 4 (=8/2):
the corank-2 "shared Delta-block" coupling raises the resolved codim from 3 to 8. So on the corank-2
stratum the threshold-only leaf data UNDER-counts the codim — it models the loss as LESS singular than
it is. The achiever-path LOWER bound (hdiv) is corank-immune (a single diverging leaf suffices), but the
UPPER bound (hfin) must control EVERY stratum.

THE QUESTIONS:
  (1) Is hfin PROVABLE from this combinatorial leaf family? To prove the actual integral finite by the
      leaf-sum, you need the leaves to correspond to GEOMETRIC charts that COVER (-1,1)^N up to measure
      zero, with a per-chart upper change-of-variables INT_{chart}|F|^{-c'} <= C_i INT model_i. Does the
      threshold-only (d,k,h) leaf family give such a valid cover? Or does the corank-2 stratum (where
      threshold-only undercounts the codim) make the per-chart bound FALSE there — i.e. on the corank-2
      chart, |F|^{-c'} is LARGER than the model monomial^{-c'} predicts, so the bound fails and the
      cover is invalid?
  (2) Sharpen: if threshold-only models (3,3,4)'s binding stratum as codim 3 (rlct 3/2) but the true
      codim is 8 (rlct 4), then for c' in (3/2, 4): the MODEL monomial integral on that leaf would
      DIVERGE (c' above the model threshold 3/2), so that leaf is NOT in the "leaf-sum finite" regime —
      does that mean the hfin hypothesis (leaf-sum finite) is only satisfied for c' < 3/2, NOT up to
      minAdm/2=4? If so, hfin as stated would be VACUOUSLY satisfiable but USELESS (it would only give
      rlct >= 3/2, not >= 4) UNLESS the leaf threshold data is the TRUE resolved codim, not threshold-
      only. Which is it? Reconcile: the atlas's PROVEN threshold_ge says every leaf threshold >= minAdm/2
      = 4 — so the (3,3,4) leaves must carry threshold >= 4, NOT 3/2. How can a threshold-only leaf carry
      threshold 4 if threshold-only computes codim 3? Is the atlas's leaf data actually the coupled
      (true) codim, or is there a tension between "threshold_ge proven" and "threshold-only undercounts"?
  (3) Net: is the hfin upper-bound atom REACHABLE from this atlas (and if so, what geometric cover +
      per-chart bound discharges it, validated on (2,2,2) and (3,3,4)), OR is there a precise
      OBSTRUCTION (the corank-2 stratum the threshold-only leaves cannot validly cover, and what
      resolving it needs — e.g. the full coupled-diag(b) resolution charts that carry the symbolic
      coupling, not just the multiplicity)?

CONSTRAINT: proven-from-scratch. The cited Aoyagi/Watanabe analytic bound (rlct >= codim/2) is NOT
allowed as a shortcut — the resolution must be exhibited. So "just cite the bound" is off the table.
</task>

<output_contract>
1. Answer (1): does the threshold-only leaf family give a valid cover with per-chart upper c-o-v, or
   does the corank-2 stratum break the per-chart bound? Derived vs conjectured.
2. Answer (2): reconcile "threshold_ge proven (>= minAdm/2)" with "threshold-only undercounts the
   corank-2 codim". Is the leaf threshold data the TRUE coupled codim or the threshold-only one? This
   determines whether hfin is useful or vacuous.
3. Answer (3): REACHABLE (the cover + per-chart bound, validated on (2,2,2),(3,3,4)) or OBSTRUCTION (the
   uncovered/mis-covered stratum + what resolving it needs).
4. Flag derived vs conjectured. Exact algebra for any codim / threshold claim.
</output_contract>

<grounding_rules>
- The monomial threshold of prod x_i^{2k_i} with Jacobian weight prod x_i^{h_i} is min_{k_i!=0}(h_i+1)/(2k_i).
- A resolution cover upper bound needs charts covering the domain up to null + per-chart |F o phi| >=
  c0 * model (so |F|^{-c'} <= C model^{-c'}); a chart that UNDER-resolves (models F as less singular)
  gives a FALSE per-chart bound.
- I am withholding my tentative conclusion (I suspect a tension in (2) that is the crux). Reason from
  the setup; the (3,3,4) threshold-only=3 vs true=8 fact is exact (prior certificate).
</grounding_rules>
