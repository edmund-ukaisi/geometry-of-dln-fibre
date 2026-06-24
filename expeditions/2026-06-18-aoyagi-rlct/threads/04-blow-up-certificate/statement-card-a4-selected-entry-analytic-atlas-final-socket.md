# Statement card - A4 selected-entry analytic atlas final socket

Status: Lean bridge landed.

Reproduction:
`reproduction-selected-entry-analytic-atlas-final-socket-a4.md`.

Independent review:
`review-selected-entry-analytic-atlas-final-socket-a4.md`.

## Target

Add a downstream bridge from a supplied
`SelectedEntryAnalyticAtlasBoundary` to the existing chart-final Theorem 2
socket.

The bridge must consume, rather than prove:

- selected-width provenance;
- the chart-level extraction hypothesis;
- the finite Theorem 2 exponent formula.

## Lean Slice

Lean now adds

```text
DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasFinalBridge
```

with

```text
SelectedEntryAnalyticAtlasBoundary.theorem2SuppliedChartFinalBoundary_of_selectedWidths_eq_reduced_of_extractionHypothesis_of_finiteExponentFormula
```

The theorem returns

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  B.chartCertificate L ell H r cuts m data lambda poleOrder
```

from:

```text
hselected :
  m = aoyagiSelectedReducedWidths H r cuts

hNC :
  B.chartCertificate.ExtractionHypothesis lambda poleOrder

hFormula :
  AoyagiTheorem2FiniteExponentFormulaHypothesis
    B.exponentData L ell H r m data.
```

The proof uses only the definitional equality
`B.exponentData = B.chartCertificate.exponentData`.

## Nonclaims

The theorem does not construct an analytic atlas, chart coverage, transition
regularity, source production, branch termination, the extraction hypothesis,
finite Theorem 2 formulas, active-ratio lower bounds, chart counts, pole
order, or RLCT.

Active-ratio or chart-count wrappers may be added later as convenience
adapters, but they must remain explicit finite-arithmetic plumbing.

## Verification

Focused verification:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasFinalBridge
```

passed on 2026-06-24.
