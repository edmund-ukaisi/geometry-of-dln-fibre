# Reproduction - A2 Case 2 passive theta source-chart readback left inverse

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a local inverse theorem for
the concrete source chart, not endpoint-sector measurability or Haar transport.

## Question

Can the direct source-family chart remember the whole full passive theta
coordinate, not only its retained-passive source data and selected-entry
residual readout?

Answer: yes, locally on the punctured determinant sector.  The source family
determines the endpoint retained-passive data by `sourceReadback`; transporting
that data back along the endpoint equivalences recovers the passive fields, and
the selected-entry inverse readout recovers `yNext`.

## Setup

For an endpoint source family `X`, define a theta readback as follows.  Let

```text
E(X) =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W2 B2 U0 hU0 X

data(X) =
  sourceReadback E(X)
```

where `data(X)` is endpoint-indexed retained-passive nonredundant data.  Define

```text
readback(X).A1passive = data(X).A1passive
readback(X).F2 p      = data(X).F2 p submatrix id (e p.castSucc)
readback(X).A3 p      = data(X).A3passive p submatrix (e p.castSucc.succ) id
readback(X).Ctop      = data(X).Ctop
readback(X).F3        = data(X).F3 submatrix (e (Fin.last 2)) id
readback(X).yNext     = case2PassiveThetaEndpointInverseReadout ... X.
```

The `submatrix` operations undo `endpointTransport e`: the endpoint data was
formed by submatrixing original passive fields along `(e q).symm`, so
submatrixing back along `e q` returns the original finite matrix.

## Calculation

Let

```text
sourceChart theta =
  case2PassiveThetaEndpointSourceChart W2 B2 n hS hcont hnext hU0 eNext e theta.
```

The existing local source chart theorem gives an open neighborhood `V` of any
base theta point in the determinant sector with nonzero selected pivot such
that for every `theta in V`,

```text
sourceReadback E(sourceChart theta)
  =
case2PassiveThetaEndpointRetainedData n hS hcont hnext theta eNext e
```

and

```text
case2PassiveThetaEndpointInverseReadout ... (sourceChart theta)
  =
theta.yNext.
```

Unfolding endpoint retained data,

```text
case2PassiveThetaEndpointRetainedData theta
  =
(case2PassiveThetaRetainedData theta).endpointTransport e.
```

The retained passive fields before endpoint transport are exactly the fields
stored in `theta`:

```text
A1passive = theta.A1passive
F2        = theta.F2
A3passive = theta.A3passive
Ctop      = theta.Ctop
F3        = theta.F3
```

After rewriting `data(sourceChart theta)` by the `sourceReadback` equality, the
definition of `readback` applies the inverse submatrix maps.  For example,

```text
((theta.F2 p).submatrix id (e p.castSucc).symm).submatrix id (e p.castSucc)
  =
theta.F2 p
```

and similarly for `A3passive` and `F3`.  The `A1passive` and `Ctop` fields are
unchanged by endpoint transport.  Together with the selected-entry readout
equality for `yNext`, this proves

```text
readback (sourceChart theta) = theta
```

for every `theta in V`.

## Lean Target

Add the concrete readback map and local left-inverse theorem to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Suggested public names:

```text
case2PassiveThetaEndpointSourceChartReadback
case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
```

## Nonclaims

This slice does not prove endpoint-sector image measurability,
`case2PassiveThetaEndpointSectorSet` is open/measurable, exact passive-sector
Haar transport, determinant-chart Haar transport, raw-order Haar transport,
source-prior comparison, source-rank coverage, normal crossings, pole order, or
RLCT extraction.  It is a source-chart left inverse on a local punctured
determinant sector.
