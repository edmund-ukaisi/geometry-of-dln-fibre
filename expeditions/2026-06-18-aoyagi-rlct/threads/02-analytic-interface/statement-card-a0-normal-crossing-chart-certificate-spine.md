# Statement card - A0 normal-crossing chart-certificate spine

## Lean Names

Files:

- `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`
- `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.exponentData`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.mem_exponentData_activePairs`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.ExtractionHypothesis`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.ExtractionHypothesis.lambda_eq_exponentMinimum`
- `DLNFibre.DLN.Aoyagi.AoyagiNormalCrossingChartCertificate.ExtractionHypothesis.theta_eq_exponentOrder`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.toSuppliedFinalBoundary`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.lambda_eq_theorem2Lambda_fromCeilData`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.poleOrder_eq_theorem2OrderFormula`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula`

## Claim

A source-facing normal-crossing chart certificate has a precise finite spine:
finite charts and coordinates, chart maps, coordinates, monomial identities
for the loss and Jacobian-prior factor, unit witnesses, and finite exponent
arrays.  Forgetting the chart-level data gives the existing finite exponent
interface.

## Proved

Lean proves only structural projections and compositions:

- a chart certificate projects to `AoyagiNormalCrossingExponentData`;
- active coordinates in the projection are exactly coordinates with positive
  chart-certificate loss exponent;
- a chart-level extraction hypothesis projects to the existing exponent-data
  extraction hypothesis;
- the chart-level final boundary projects to the existing supplied final
  boundary and therefore inherits the existing lambda/order formula
  projections.

## Assumed / Cited

The chart-level extraction hypothesis is still the normal-crossing-to-RLCT
analytic citation.  The chart certificate does not by itself prove that the
analytic hypotheses hold.

## Deferred

Hironaka resolution, proper analytic maps, chart coverage, coordinate
validity, analytic nonvanishing of units, change of variables, integrability
and zeta-pole extraction, Aoyagi Lemma 1, prior-independence, construction of
the certificate from the blow-up recursion, finite exponent formula equality,
Lemma 5 counts, pole order without A0, and RLCT extraction.

## Verification

Focused verification targets:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.NormalCrossingInterface
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean
```

Full closeout should also run:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

Independent xhigh review passed:
`review-normal-crossing-chart-certificate-spine-a0.md`.
