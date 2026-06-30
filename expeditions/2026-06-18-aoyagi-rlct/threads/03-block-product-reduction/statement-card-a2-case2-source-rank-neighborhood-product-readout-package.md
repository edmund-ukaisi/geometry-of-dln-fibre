# Statement Card - A2 Case 2 source-rank-neighborhood product readout package

## Claim

For the concrete Case 2 endpoint p.13 product source chart, the full small-ball
readout package holds eventually along any fixed source-rank stratum
neighborhood:

```text
eventually theta in nhdsWithin theta0 sourceStratum,
  forall u in ball 0 R,
    regularCoordinateMap(productSourceChart(theta,u)) = u
    residualCoordinateMap(productSourceChart(theta,u))
      =
    residualCoordinateMap(sourceChart theta)
    regularReadback(productSourceChart(theta,u)) = u
    selectedInverseReadout(productSourceChart(theta,u))
      =
    selectedInverseReadout(sourceChart theta)
    sourceReadback(productSourceChart(theta,u)) has the p.13 product fields
```

Public Lean name:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package_nhdsWithin_source
```

The older two-coordinate neighborhood theorem

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq_nhdsWithin_source
```

now projects its two eventual coordinate-map conclusions from this full package.

## Inputs Used

- the concrete passive-theta endpoint source chart;
- a base point `theta0`;
- a source-rank stratum `paperEndpointFixedBaseSourceRankStratum ... r rEdge`;
- a positive radius cap `Rmax`;
- the global uniform Case 2 small-ball readout package.

## Output

Lean returns `R > 0`, `R <= Rmax`, and a single eventual statement along
`nhdsWithin theta0 sourceStratum`.  The readout facts are identical to the
global Case 2 small-ball package, but now presented in the filter shape used by
source-rank-local arguments.

## Proof Shape

Apply

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_readout_package
```

and convert the resulting `forall theta` statement to an eventual statement by
`Filter.Eventually.of_forall`.  No source-rank openness or coverage theorem is
used.

## Nonclaims

This is not source-rank coverage and not source-image equality.  It does not
identify an original/source prior, prove Haar/Jacobian transport, establish
normal crossings, compute pole order, or extract an RLCT.

## Status

Focused direct Lean check, focused module build, full local `lake build
DLNFibre`, `scripts/sorries`, `git diff --check`, and direct axiom probe
passed.  The axiom footprint is `[propext, Classical.choice, Quot.sound]`.
