# Reproduction - A2 Retained-Passive Open Punctured-Sector Readout

Date: 2026-06-29.

Status: Lean theorem landed; focused build passed; xhigh review PASS.

Predecessor frontier:

```text
reproduction-a2-retained-passive-passive-variable-sector-transport.md
statement-card-a2-retained-passive-passive-variable-sector-transport.md
review-a2-retained-passive-passive-variable-sector-transport.md
```

## Question

Can the passive-variable selected-entry source chart be packaged with an open
determinant-domain source readback and the fixed-pivot selected-entry inverse
on the nonzero-pivot sector?

Answer: yes.  The result is a pointwise open-sector inverse/readout theorem.
It does not assert a measure equality, determinant-chart Haar transport,
external source-prior comparison, selected-entry source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT.

## Input Algebra

For the continuing Case 2 selected-entry chart, let

```text
center    = case2ResidualBlockPivotEntries n S (J+1),
pivotNext = (J+2, J+2) in center,
rho       = Fin (finrank R U0),
kappaRaw  = case2PostPivotTwoEdgeDomain n S J tau,
kappaEnd  = throughSubspaceEndpointComplementIndex (...).
```

The passive retained fields are

```text
A1passive : eta -> Fin 1 -> Matrix rho rho,
F2        : eta -> forall p : Fin 2, Matrix rho (kappaRaw p.castSucc),
A3passive : eta -> forall p : Fin 1, Matrix (kappaRaw p.castSucc.succ) rho,
Ctop      : eta -> Matrix rho rho,
F3        : eta -> Matrix (kappaRaw (Fin.last 2)) rho.
```

For `z = (theta,y)`, define

```text
retainedData z =
  endpointTransport e
    (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      n hS hcont hnext
      (A1passive theta) (F2 theta) (A3passive theta)
      (Ctop theta) (F3 theta) y eNext).
```

The existing open source-readback theorem gives an open set `U` containing
the base point `z0` such that for each `z in U`, if

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData z),

E z =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W2 B2 U0 hU0 (sourceChart z),
```

then `sourceChart z` lies in the retained-passive p.13 local source and

```text
sourceReadback (E z) = retainedData z.
```

## Residual Readout

The with-passive endpoint residual-factor identity gives

```text
residualFactorProduct (retainedData z).C (Fin.last 2) 0
  =
AoyagiResidualBlockCoordinateIndex.matrix
  (fun c =>
    SelectedEntrySignedBox.CenterCoord.chartMap
      pivotNext y (residualCoordEquiv c)).
```

Using `sourceReadback (E z) = retainedData z`, the residual readout from
`sourceReadback (E z)` is therefore the selected-entry chart map:

```text
fun i : center =>
  value
    (residualFactorProduct (sourceReadback (E z)).C (Fin.last 2) 0)
    (residualCoordEquiv.symm i)
=
SelectedEntrySignedBox.CenterCoord.chartMap pivotNext y.
```

On the punctured sector `y pivotNext != 0`, Lean already has

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
```

so the selected-entry inverse of that residual readout recovers the original
selected-entry residual coordinates:

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
  pivotNext residualReadout
=
y.
```

## Lean Theorem

The landed theorem is:

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean
```

It reuses the open set from

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
```

and proves, for every `z` in that open set, local-source membership,
source-readback equality, and the nonzero-pivot selected-entry inverse
readout.

## Nonclaims

No measure pushforward, determinant-chart Haar transport, source-prior
comparison, selected-entry source-image equality, source-rank coverage,
normal crossings, pole order, or RLCT extraction is proved by this theorem.
