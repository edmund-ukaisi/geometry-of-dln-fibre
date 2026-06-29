# A2 Case 2 endpoint-transport continuous-density small-box two-sided iff

## Claim

For the endpoint-transported explicit continuing Case 2 selected-entry chart,
the generic retained-passive positive-continuous-density small-box theorem
applies without exposing the abstract retained-passive datum, determinant proof,
residual-coordinate equivalence, residual-factor readout, or determinant-chart
a.e. measurability as hypotheses.

The conclusion is the same source-stratum two-sided local handoff:

```text
actual loss-density integral over (mu.restrict (U inter sourceStratum)).prod nu
  is finite
iff
residualNegPowerIntegrableOn (fun E => E) (U inter sourceStratum) mu t.
```

The radius is produced first from the continuous positive density:

```text
exists R dρ Dρ, 0 < R and R <= Rmax and 0 < dρ and 0 <= Dρ.
```

Only after that choice does the theorem require the selected-entry small-box
condition:

```text
0 <= delta,
forall i, Rres i <= delta,
delta^2 * (1 + #(center.erase pivotNext) * delta^2) <= R^2.
```

## Reproduction

Let

```text
center    = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center,
retainedData(yNext)
  = (case2PostPivotSelectedEntryRetainedPassiveData
      n hS hcont hnext yNext eNext).endpointTransport e,
sourceChart(yNext)
  = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      W2 B2 U0 hU0 (retainedData yNext).
```

The existing Case 2 endpoint-transport reproduction gives:

1. `retainedData(yNext).detChart`;
2. the residual-coordinate equivalence
   `case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs ...`;
3. the stored residual-factor product identity

   ```text
   residualFactorProduct (retainedData yNext).C (Fin.last 2) 0
     = matrix (chartMap pivotNext yNext residualCoordEquiv).
   ```

The existing Case 2 continuity reproduction gives continuity of the map into
the determinant-chart subtype.  Therefore that map is a.e. measurable for the
finite selected-entry signed-box product measure.

These are exactly the abstract inputs required by the generic retained-passive
small-box theorem.  Applying that theorem with `M = 1`, `W = W2`, `B = B2`,
`pivot = pivotNext`, and `Cedge = fun E => E` gives the Case 2 statement.

No new numerical or algebraic calculation is introduced here.  This is a
composition of:

- `reproduction-a2-case2-endpoint-transport-chart-produced-finite-integral.md`;
- `reproduction-a2-case2-retained-passive-data-center-matrix-handoff.md`;
- `reproduction-a2-retained-passive-small-box-chart-produced-residual-bound.md`.

## Boundary

This theorem does not choose `Rres` or `delta`, and it does not assume or prove
the selected-entry critical inequality.  It does not prove the source-stratum
loss comparison hypotheses, source-rank coverage, selected-entry source/image
equality, original source-prior transport, Jacobian comparison, normal
crossings, pole order, or RLCT.
