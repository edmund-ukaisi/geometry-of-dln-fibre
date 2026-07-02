# Reproduction - A2 Case 2 enlarged following-factor passive sector

Date: 2026-07-02.

Status: enlarged passive-sector source domain and finite-coordinate support.

## Pen-and-Paper Check

The previous passive-theta coordinate has the form

```text
theta = (passive fields, yNext),
```

where `yNext` parametrizes the selected-entry residual block.  In the two-edge
post-pivot retained-passive datum, the active `C` family has two entries:

```text
C(0) : residual columns -> endpoint columns,
C(1) : residual rows -> residual columns.
```

The selected-entry center coordinates determine `C(1)`.  The following factor
`C(0)` is not determined by the selected-entry center unless we restrict to the
section used by the old passive-theta map.  To obtain an independent chart
coordinate for the full displayed p.13 active `C` tuple, the source domain must
be enlarged to

```text
Case2PassiveThetaWithFollowingFactor =
  Case2PassiveTheta x Matrix (Case2ResidualColIndex n S (J+1)) tau Real.
```

The determinant sector is unchanged: it only asks that `Ctop` and passive
`A1` blocks have unit determinant.  The new following-factor matrix is a
regular active `C(0)` coordinate and introduces no determinant condition.

## Lean Slice

The new domain and finite-coordinate wrappers are in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSector
```

with names

```text
Case2PassiveThetaWithFollowingFactor
case2PassiveThetaWithFollowingFactorRetainedData
case2PassiveThetaWithFollowingFactorEndpointRetainedData
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
case2PassiveThetaWithFollowingFactorEndpointSectorSet
```

The retained data is defined by the earlier enlarged constructor

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor
```

using `theta.yNext` for `C(1)` and the free following-factor matrix for `C(0)`.

The formalized support lemmas prove:

- continuity of the retained-data and topology-tuple maps;
- determinant-chart membership before and after endpoint transport;
- endpoint topology-tuple membership in the determinant-chart set.

## Nonclaims

This slice does not define an endpoint source chart/readback for the enlarged
domain, prove local source-image measurability, prove injectivity, identify a
reference measure, prove a Jacobian or density formula, prove source-image
coverage, or extract any normal-crossing/RLCT statement.
