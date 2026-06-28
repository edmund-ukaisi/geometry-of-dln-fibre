# Statement card - A2 Case 2 inverse-Jacobian density-continuous finite integral

## Lean target

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map_continuousAt_pos_density
```

## Mathematical content

In the endpoint-transported Case 2 selected-entry branch, positive continuity
of the transported density at the fixed-base regular-coordinate center supplies
the local density nonnegativity and upper-bound hypotheses needed by the
raw-order inverse-Jacobian finite-integral socket, after shrinking the
regular-coordinate radius.

## Inputs

- the existing data and typeclass assumptions of the raw-order inverse-Jacobian
  Case 2 finite-integral theorem;
- `0 < Rmax`, `0 < c`, `0 < t`;
- determinant-chart pushforward identity
  `m.restrict Sdet = Measure.map chart weightedBox`;
- positive selected-entry radii and selected-entry critical inequality;
- `ContinuousAt density (base, 0)`;
- `0 < density (base, 0)`;
- the local loss lower bound on `ball 0 Rmax`.

## Output

The theorem should return `R`, `C`, and `U` such that

```text
0 < R,
R <= Rmax,
0 <= C,
IsOpen U,
base in U,
```

and the same regular-coordinate finite-integral conclusion holds with radius
`R`, source measure

```text
mu =
  Measure.map rawChart
    ((m.restrict T).withDensity inverseJacobianDensity),
```

and restriction to `U inter sourceStratum`.

## Nonclaims

This does not remove the determinant-chart pushforward hypothesis.  It does
not identify Haar measure or an external source prior, prove chart coverage,
prove source-rank coverage, construct normal crossings, compute pole order, or
extract RLCT.
