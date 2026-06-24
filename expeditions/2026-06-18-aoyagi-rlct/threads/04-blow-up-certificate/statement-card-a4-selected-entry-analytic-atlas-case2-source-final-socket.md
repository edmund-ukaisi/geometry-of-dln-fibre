# Statement card - A4 selected-entry analytic atlas Case 2 source final socket

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-selected-entry-analytic-atlas-case2-source-final-socket-a4.md`.

## Target

Add a narrow downstream bridge from `SelectedEntryAnalyticAtlasBoundary` to the
existing Case 2/A0 chart-final socket.

The source-production predicate should carry a displayed continuing Case 2
source-chart center-square/formal-Jacobian certificate, an active coordinate in
the supplied chart certificate, and a
`Case2DisplayedContinuingA0ExponentCoordinateBridge` for that coordinate.

## Lean Artifacts

Add a module, expected name:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasCase2FinalBridge.lean
```

Expected declarations:

```text
SelectedEntryCase2DisplayedA0SourceProductionData
SelectedEntryCase2DisplayedA0SourceProduction
SelectedEntryAnalyticAtlasBoundary
  .theorem2SuppliedChartFinalBoundary_of_case2DisplayedA0SourceProduction
```

The theorem should consume:

- `B : SelectedEntryAnalyticAtlasBoundary ... SelectedEntryCase2DisplayedA0SourceProduction ...`;
- selected-width provenance;
- chart-level extraction hypothesis;
- displayed center-card equals Theorem 2 lambda formula;
- global active-ratio lower bound;
- chart-count equality at the displayed ratio;
- chart-count upper bound.

It should return:

```text
AoyagiTheorem2SuppliedChartFinalBoundary B.chartCertificate ...
```

## Nontriviality Test

The `SourceProduction` predicate must not be `True`, finite coordinate
postdata alone, or a wrapper around
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`.  It
must contain the displayed Case 2 source certificate and the A0
exponent-coordinate bridge for the same supplied chart certificate.

## Expected Proof

The proof should unwrap the nonempty source-production payload and call:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge
  .theorem2SuppliedChartFinalBoundary_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
```

No analytic construction should occur in this theorem.

## Verification

Controller verification passed:

```text
cd lean && LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasCase2FinalBridge.lean
cd lean && LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasCase2FinalBridge
cd lean && LEAN_NUM_THREADS=1 lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

The intended `scripts/lb` route was not available in this sandbox because the
shared `~/.lake-shared` lock write requires unsandboxed execution.  The local
single-worker build route passed.
