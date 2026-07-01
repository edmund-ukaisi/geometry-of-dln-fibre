# Statement Card - A2 Case 2 raw-order reference same-shrink package

## Claim

There is one local Case 2 determinant/punctured-sector shrink `V subset G` on
which the named raw-order reference image simultaneously has:

- support on the raw-order source-recursive determinant chart;
- passive-field domination handoff to that named image measure;
- endpoint-reference image pushforward through `topologyTupleEdgeRawOrder`;
- raw-order source-chart pushforward to the direct source-chart reference image;
- raw-density transport through the p.13 raw-order source chart.

Expected public Lean name:

```text
exists_open_subset_case2PassiveThetaRawOrderReferenceImage_same_shrink_package
```

## Inputs Used

- `case2PassiveThetaRawOrderReferenceImageMeasure`;
- `case2PassiveThetaEndpointReferenceImageMeasure`;
- the local raw-order/source-chart two-stage theorem;
- local determinant-chart support for the endpoint map;
- `prod_le_smul_prod_of_le_smul_left`;
- `map_le_smul_map_of_le_smul_aemeasurable`;
- `measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict`.

## Nonclaims

No raw-Haar identification or raw-Haar pushforward, determinant-chart Haar
domination, full determinant-chart Haar target, exact Haar transport, Haar or
scalar normalization, full chart/image coverage, p.13 source coverage,
source-image coverage, source-rank coverage, original DLN source-prior or
original-volume transport, Jacobian formula for `Y`, bounded-density
construction, prior-density transport, normal crossings, pole order, or RLCT
extraction is claimed.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.  Xhigh Lean/API and
source-boundary reviewers passed the statement boundary.
