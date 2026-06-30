# SCOPE — is #44 (`deepest_regular_core_normal_form`) reachable via the new §SEL IFT chart?

**VERDICT: NO — the §SEL chart does NOT short-circuit #44. Not a "via-the-new-chart" win.**
But #44 is ALSO not a fresh research wall: it is ALREADY architecturally decomposed (green-modulo-two-
gates) via its OWN gauge-slice chart, and the genuine remaining content is two specific obligations that
the §SEL chart does not touch. Decorrelated: my repo reading + Codex xhigh (read-access deep-dive) AGREE
on the bottom line. Scope branch `scope/p44-via-chart` (off canonical HEAD; NO genm-d1hchart writes).

## Why the §SEL chart does NOT reach #44 (the load-bearing distinction)

The §SEL chart and the #44 gauge chart are DIFFERENT objects for DIFFERENT purposes:
- **§SEL chart** (`S1IFTChart`, genm-d1hfin's D1 leg): straightens `nReg` selected loss-MINORS to
  coordinates `s`; the complement is a generic projection, and the residual `q` is a GENERIC `C¹`
  sum-of-squares (`D1IFTResidualProducer`: `q : … → EuclideanSpace ℝ (Fin n)`, `ContDiff ℝ 1`). It yields
  the COMPARISON inequality `rlctAt deepest ≤ rlctAt v` (the D1 ≥-leg), and it CONSUMES #44's value as the
  hypothesis `hDeepest`. It does not produce an absolute value.
- **#44 gauge chart** (`DeepestGaugeChart`, the `C_s = [[I_r+X,Y],[Z,T]]` rank-`r` gauge slice): the
  complement block `T` IS the reduced loss `dlnLoss (H−r) 0` by construction, so the residual's RLCT is
  `rlctAtOn(dlnLoss (H−r) 0) 0` — which R1 identifies with `lambdaCore(H−r)`. This is the chart #44 needs.

The §SEL `q` is NOT identified with the reduced loss (it's a generic C¹ residual whose RLCT is opaque), so
plugging the §SEL chart into the deepest point gives `rlctAt deepest = nReg/2 + rlctAtOn(q(0,·)²)` with NO
handle on `rlctAtOn(q(0,·)²) = lambdaCore`. The chart "defers the hard work to the same outstanding
result" (Codex). The deepest-point-is-a-special-case-of-general-v intuition is TRUE but unhelpful: the
generic chart loses exactly the reduced-loss structure #44 exploits.

## What #44 ACTUALLY is (already decomposed — `DeepestNormalFormWiring` + `DeepestGaugeChart`)

`deepest_normal_form_of_value` (conditional #44) proof = `deepest_regular_core_reduces ▸ hRValue`
(one-liner once the two gates land). The Skeleton `deepest_regular_core_normal_form` sorry collapses to
`exact deepest_normal_form_of_value … hGne hRValue`. The two gates:

1. **Value-free reduction** `deepest_regular_core_reduces` (`DeepestGaugeChart`, ROUTE-FIRST scaffold, 2
   sorries): `rlctAt deepest = nReg/2 + rlctAtOn(dlnLoss (H−r) 0) 0`. 7 sub-lemmas — 5 reachable via green
   primitives (rank-exact, transport, reduced-core-identification, smooth-split), the HEAVY one =
   **sub-lemma 3 `deepest_gauge_squeeze_exists` (#44c, "the sub-34 obligation")** = the gauge-slice chart
   existence (unit-Jacobian, routes through `rlctAtOn_unit_invariant_aux` + germ-locality, NOT measure-
   preserving). This is the ~600–1500 LoC heavy piece — and the §SEL chart does NOT supply it (different
   chart, different complement). + the `hGne` reduced-core germ-nonvanishing precondition.
2. **R1 core-value** `hRValue : rlctAtOn(dlnLoss (H−r) 0) 0 = ofReal(lambdaCore (H−r))` — R1's lane
   (`resolution_charts` ▸ A1 `lambdaCore_eq_clean`; `routeLayerAtlas_value_eq_lambdaCore` exists gated on
   `1 ≤ minAdm` + the cited S2 monomial-integral axiom). Codex flags the general Route-M recursion wiring
   here as the residual wall; the leaf/value arithmetic (`D1ChartProducerL2Build`, `DeepestBaseL1` L=1
   base) is sorry-free.

## The genuine status + the route that WOULD close #44

NOT bounded-via-§SEL-chart; NOT a fresh wall. The two open obligations are:
- (#44c) the **deepest gauge-slice chart existence** `deepest_gauge_squeeze_exists` — the heavy unit-
  Jacobian gauge chart (this is "the heavy gauge-slice" the docstring named; the §SEL machinery is
  orthogonal to it). HEAVY but the bedrock (`rlctAtOn_unit_invariant_aux`, germ-locality, the
  smooth-split sub-lemmas) is green; ROUTE-FIRST scaffolded.
- (R1) the **Route-M recursion value** `rlctAtOn(dlnLoss M 0) 0 = lambdaCore M` general wiring (modulo S2).

★ ONE genuine partial win the §SEL/D1 machinery DOES give: at MIDDLE strata the D1 ≥-leg already uses the
chart-transfer to COMPARE; #44 is only needed at the deepest point. So #44 + the D1 comparison together
give the L2 headline — but #44 itself is gated on the gauge chart + R1, not the §SEL chart.

## Recommendation
Do NOT pursue "#44 via the §SEL chart" — it's a category mismatch (minor-straightening vs gauge-slicing).
The reachable lever is the EXISTING decomposition: drive `deepest_gauge_squeeze_exists` (#44c, the heavy
gauge chart — its own sub-thread, sub-34) + close the Route-M recursion value (R1). Both are HEAVY but
ROUTE-FIRST scaffolded with green bedrock; neither is a fresh research wall. `product_reduction` then
follows from #44 (one `▸`).

Artefacts: `p44-reachability-{prompt,answer}.md` (the decorrelated Codex consult, read-access deep-dive).
