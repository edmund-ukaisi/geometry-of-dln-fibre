# Statement card - A4 Case 2 source-selected finite transition

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryChartMap_transition_eq_of_target_normalized_ne_zero`
- `case2SourceSelectedChartMapOfMem_transition_eq_of_target_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_transition_chartMap_eq_of_target_normalized_ne_zero`

## Claim

For two selected-entry residual-block pivots, the source-selected finite chart
maps agree on the overlap where the target normalized coordinate is nonzero.

If a source chart has finite values `d_i = u*x_i` and the target normalized
coordinate satisfies `x_q != 0`, then the target chart data

```text
u_q = u*x_q,
y_i = x_i/x_q
```

produce the same finite residual-block center value.

## Inputs Kept Explicit

- source and target residual-block pivot memberships, or chart indices whose
  pivots are supplied by `finsetSubtypeChartEquiv`;
- the source selected variable `u` and ambient residual function;
- the normalized target-coordinate nonvanishing condition;
- ordered-field hypotheses only for the chart-certificate namespace wrapper.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
statement, no claim that Aoyagi displays non-top-left charts, no Q/P
reduced-block transition, no successor/suffix production, no analytic
Jacobian/volume theorem, no global normal crossings, no pole order, and no
RLCT extraction.

## Verification

Current checks passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

Independent xhigh review passed with no blocking findings.  Durable artifact:
`review-case2-source-selected-finite-transition-a4.md`.  The full build still
reports pre-existing unrelated Core/style warnings.
