# Reproduction - A2 single-edge selected-entry determinant-ball readout

Date: 2026-06-25.

Status: pen-and-paper reproduction before Lean.  This is a radius wrapper for
the one-edge selected-entry product-coordinate readout.

## Source Boundary

Aoyagi's p.13 product-coordinate formulas are used on the determinant chart
where the regular top block `Ctop` is invertible.  The previous one-edge
selected-entry slices kept this determinant-unit condition as an explicit
pointwise hypothesis:

```text
IsUnit det(Ctop(u)).
```

The finite regular-coordinate API already proves that `Ctop(0)=I`, hence
`det(Ctop(0))=1`, and by continuity there is a positive ball around the
centered regular coordinate on which the determinant remains a unit.  This
note records the formal consequence for the one-edge selected-entry family.

## Calculation

Fix a positive bound `Rmax`.  The determinant-neighborhood theorem gives
`0<R<=Rmax` such that, for every regular vector `u` with `u in ball(0,R)`,

```text
IsUnit det(Ctop(u)).
```

For the one-edge selected-entry product-coordinate family

```text
CedgeProd(y,u) =
  [ Ctop(u),          -Ctop(u) F2(u)
    -F3(u) Ctop(u),   Dbase(y) + F3(u) Ctop(u) F2(u) ],
```

where

```text
Dbase y =
  AoyagiResidualBlockCoordinateIndex.matrix
    (fun c => chartMap pivot y (residualCoordEquiv c)),
```

the pointwise determinant-chart readout applies to every `u` in the ball:

```text
regular coordinates = u,
residual coordinate c = chartMap pivot y (residualCoordEquiv c).
```

The scalar square-sum consequence also applies in the same ball:

```text
aoyagiCoordinateSquareSum (residualBlockCoordinateMap(y,u))
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

No source parameter enters the determinant argument; the same radius works for
all selected-entry parameters `y`.

## Lean Target

Add in `SelectedEntryOriginalLossLocalMeasure.lean`:

```text
exists_pos_radius_le_forall_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEuclidean_readout
```

It should call
`AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean`
and then apply the already-proved one-edge selected-entry coordinate and
square-sum readout theorems.

## Boundary

- One-edge only.
- Source-neutral determinant-ball and finite readout algebra only.
- The positive radius is local near the centered regular coordinate and can be
  chosen below a supplied `Rmax`.
- The residual-coordinate equivalence is still supplied data.
- No source coverage, source-stratum equality, source-measure transport,
  local lower bound, normal crossings, pole order, or RLCT is proved.
