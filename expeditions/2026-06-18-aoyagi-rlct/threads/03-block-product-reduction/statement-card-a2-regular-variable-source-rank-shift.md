# Statement Card - A2 Regular-Variable Source-Rank Shift

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`

## Claim

Membership in Aoyagi's source-shaped rank stratum, together with the explicit
dimension convention

```text
H(k+1) = finrank(W k),
```

supplies the endpoint rank-width bounds used by the regular-variable finite
shift:

```text
r <= H 1,
r <= H (N+1).
```

Therefore the existing finite regular-variable shift can be applied with
`L = N` without separately supplying those endpoint bounds.

## Lean Names

```text
paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds
AoyagiNormalCrossingExponentData
  .exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
AoyagiNormalCrossingChartCertificate
  .exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
AoyagiTheorem2FiniteExponentFormulaHypothesis
  .of_regularVariableCountShift_sourceRankStratum
AoyagiTheorem2FiniteExponentFormulaHypothesis
  .of_chart_regularVariableCountShift_sourceRankStratum
```

## Inputs Kept Explicit

- Source-rank-stratum membership.
- The dimension convention `H(k+1)=finrank(W k)`.
- The reduced finite minimum plus Aoyagi's regular term equals the displayed
  Theorem 2 lambda formula.
- The reduced finite order equals the displayed Theorem 2 order formula.

## Not Proved

No Aoyagi Theorem 3 analytic transport, no exact-rank openness, no
regular-suspension chart construction, no analytic ideal transport, no Aoyagi
Lemma 1, no normal-crossing chart production, no pole-order theorem, and no
RLCT theorem.  The reduced certificate remains supplied.

## Verification

Focused checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/RegularVariableShift.lean
cd lean && LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.RegularVariableShift
```

`scripts/lb` could not be used in this sandbox because `~/.lake-shared/slots`
was read-only.
