# Reproduction - A2 Case 2 endpoint-transport factor alignment

## Shape

For the displayed Case 2 two-edge endpoint family,

```text
0 = tau,
1 = Case2ResidualColIndex n S (J + 1),
2 = Case2ResidualRowIndex n S (J + 1).
```

The explicit selected-entry retained-passive datum is

```text
data :=
  case2PostPivotSelectedEntryRetainedPassiveData
    (rho := rho) n hS hcont hnext yNext eNext.
```

Its stored `C` family is Aoyagi's displayed two-edge factor family:

```text
data.C 1 = displayed post-pivot residual block,
data.C 0 = displayed free following factor.
```

The residual product order is therefore

```text
data.C 1 * data.C 0.
```

## Endpoint transport

Endpoint transport by

```text
e q : case2PostPivotTwoEdgeDomain n S J tau q ~= kappa' q
```

reindexes a stored factor by pulling the transported endpoint coordinates back
to the displayed endpoint coordinates:

```text
(data.endpointTransport e).C p =
  (data.C p).submatrix (e p.succ).symm (e p.castSucc).symm.
```

To compare this transported factor with the displayed matrix, apply the forward
endpoint equivalences as a second submatrix.  For `p = 1`,

```text
((data.endpointTransport e).C 1).submatrix (e 2) (e 1)
  =
((data.C 1).submatrix (e 2).symm (e 1).symm).submatrix (e 2) (e 1)
  =
data.C 1
  =
case2DisplayedPostPivotResidualBlock n hS hcont residual.
```

For `p = 0`,

```text
((data.endpointTransport e).C 0).submatrix (e 1) (e 0)
  =
((data.C 0).submatrix (e 1).symm (e 0).symm).submatrix (e 1) (e 0)
  =
data.C 0
  =
case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime.
```

In the selected-entry datum,

```text
residual = case2SuccessorSelectedEntrySourceResidual n hS hnext yNext eNext,
Cprime   = case2SuccessorSelectedEntrySourceCprime n hS hcont hnext yNext eNext.
```

## Boundary

This is finite endpoint reindexing and displayed Case 2 algebra only.  It does
not prove that an arbitrary fixed-base source-readback factor is this explicit
datum, and it does not prove product nonzeroness.  It supplies the `hD` and
`hF` fields only for the endpoint-transported explicit retained-passive datum.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The endpoint-transported explicit Case 2
selected-entry retained-passive datum has the displayed post-pivot residual
block and displayed free following factor after submatrixing by the forward
endpoint equivalences `e 2`, `e 1`, and `e 0`.

**Assumed.** The endpoint equivalences `e`, the successor endpoint equivalence
`eNext`, and the existing definitions of the selected-entry residual and
following factor.

**Deferred.** Product nonzeroness, fixed-pivot nonzeroness, arbitrary
`ofTopologyTuple` factor alignment, fixed-base source-readback provenance,
source-prior transport, Jacobian comparison, normal crossings, pole order, and
RLCT.
