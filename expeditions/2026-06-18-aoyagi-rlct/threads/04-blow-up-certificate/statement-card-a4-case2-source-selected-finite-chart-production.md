# Statement card - A4 Case 2 source-selected finite chart production

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_sourceSelectedChartMap_eq_value`

## Claim

Every finite value of the Case 2 residual-block center has a representative in
one of the source-selected selected-entry charts indexed by the all-pivot
finite certificate.

Equivalently, for a value on
`case2ResidualBlockPivotEntries n S J`, there exist a chart index `c`, a
selected variable `u`, and ambient residual coordinates `residual` such that
the source-selected chart map for the pivot enumerated by `c` equals that
value.

## Inputs Kept Explicit

- displayed Case 2 continuation assumptions `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- the finite residual-block center value;
- ordered-field hypotheses used by the existing selected-entry finite
  certificate layer.

## Not Proved

No analytic atlas coverage, no open-neighbourhood statement, no transition
regularity, no source production of recurrence successors or suffixes, no
claim that Aoyagi displays non-top-left source charts, no analytic
Jacobian/volume theorem, no global normal crossings, no pole order, and no
RLCT extraction.

## Verification

Focused and full checks passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build still reports pre-existing warnings in unrelated
Core modules.

Independent xhigh review passed with only a stale-status documentation finding,
now addressed.  Durable artifact:
`review-case2-source-selected-finite-chart-production-a4.md`.
