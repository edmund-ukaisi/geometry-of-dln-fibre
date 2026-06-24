# Statement Card - A6 Theorem 2 Source-Rank Regular-Shift Bridge

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/Theorem2SourceRankRegularShiftBridge.lean`

## Claim

Definition 3 source data plus A2 source-rank-stratum membership can be routed
into the supplied final Theorem 2 socket for the finite regular-variable
shifted certificate.

The bridge keeps the shifted extraction hypothesis and the reduced finite
formula obligations explicit.  Source-rank membership is used only for
source-range rank-width provenance and the endpoint bounds needed by the
finite regular-variable shift.

## Lean Names

```text
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_regularVariableCountShift
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_regularVariableCountShift
```

## Inputs Kept Explicit

- Definition 3 source data.
- Source-rank-stratum membership.
- The dimension convention `H(k+1)=finrank(W k)`.
- Extraction hypothesis for the shifted finite exponent datum or shifted chart
  certificate.
- Reduced minimum plus Aoyagi's regular term equals the displayed Theorem 2
  lambda formula.
- Reduced finite order equals the displayed Theorem 2 order formula.

## Not Proved

No construction of the reduced or shifted certificate, no regular-suspension
chart construction, no analytic ideal transport, no Aoyagi Lemma 1, no
exact-rank openness, no active-ratio lower bound, no chart-count theorem, no
normal-crossing chart production, no pole-order theorem, and no RLCT theorem
beyond the explicitly supplied shifted extraction hypothesis.

## Verification

Focused checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2SourceRankRegularShiftBridge.lean
cd lean && LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.Theorem2SourceRankRegularShiftBridge
```
