# A2 retained-passive two-edge `ofTopologyTuple` selected-entry product adapter

Status: Lean target; pen-and-paper reproduction before formalisation.

## Claim

For a retained-passive topology tuple with exactly two active residual factors
(`M = 1`), suppose its two stored `C` factors become Aoyagi's displayed Case 2
post-pivot residual block and following free factor after endpoint
reindexing.  If the displayed two-edge product has the selected-entry
center-coordinate readout entrywise, then the whole retained-passive residual
factor product from the last endpoint to endpoint `0` is the selected-entry
matrix.

This is an adapter from

```text
ofTopologyTuple z
```

to the existing retained-passive data-level theorem.  It is not a theorem
about a longer suffix.

## Pen-and-paper reproduction

Let the endpoint family have three endpoints

```text
kappa 2, kappa 1, kappa 0
```

and let

```text
D = (ofTopologyTuple z).C 1,
F = (ofTopologyTuple z).C 0.
```

Since the suffix has exactly two edges, the residual factor product from the
last endpoint to endpoint `0` is the adjacent product

```text
residualFactorProduct (ofTopologyTuple z).C 2 0 = D * F.
```

The hypotheses reindex the two factors as

```text
D.submatrix e2 e1 = case2DisplayedPostPivotResidualBlock,
F.submatrix e1 e0 = case2DisplayedPostPivotFreeFollowingFactor.
```

The already proved retained-passive data-level Case 2 theorem applies to the
data object

```text
data = ofTopologyTuple z.
```

Its proof is finite matrix algebra: the submatrix of the adjacent product is
the product of the two reindexed displayed factors, and the supplied entrywise
hypothesis identifies every resulting entry with

```text
CenterCoord.chartMap pivot y (residualCoordEquiv c).
```

Therefore

```text
residualFactorProduct (ofTopologyTuple z).C 2 0
  = matrix (fun c => CenterCoord.chartMap pivot y (residualCoordEquiv c)).
```

## Scope boundary

The two-edge condition is essential.  For a longer suffix, replacing one
adjacent Case 2 window gives

```text
P_left * (selectedEntryMatrix * P_right),
```

with the outside factors still present.  This adapter does not prove those
outside factors are identities, harmless, invertible in a loss-preserving way,
or absorbed by a chart.  It also does not prove zero-locus nullity,
chart-side positivity, finite negative-power integrability, density transport,
normal crossings, pole order, or RLCT extraction.
