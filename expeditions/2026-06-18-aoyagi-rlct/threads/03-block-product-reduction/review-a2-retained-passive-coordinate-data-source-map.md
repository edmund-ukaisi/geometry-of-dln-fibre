# Review - A2 retained-passive coordinate-data source map

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Kant the 3rd`.

## Scope

Audit the finite retained-passive coordinate-data/source-map API in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.RetainedPassiveCoordinateData
ChartLocalSuffixState.RetainedPassiveCoordinateData.solvedA1
ChartLocalSuffixState.RetainedPassiveCoordinateData.solvedA3
ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix
ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_readbacks_eq_targets
```

The review checked field contents, projection order, signs, terminal `F2`
condition, reuse of the solved-family wrapper, and the nonclaim boundary.

## Verdict

PASS.

## Checks

`RetainedPassiveCoordinateData` has exactly the expected six fields:

```text
A1seed, F2, A3seed, C, Ctop, F3.
```

The projections delegate in the expected order:

```text
solvedA1 = retainedPassiveSolvedA1(A1seed,Ctop),
solvedA3 = retainedPassiveSolvedA3(solvedA1,A3seed,C,F3),
edgeMatrix = retainedPassiveFixedBaseEdgeMatrix(solvedA1,F2,solvedA3,C).
```

The readback theorem reuses
`retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets` under
`F2_last=0`, passive `A1seed` determinant-unit hypotheses, and `det(Ctop)`
unit.  The per-edge readback uses `data.F2 p.castSucc`, matching the upstream
fixed-base theorem, and the terminal condition remains
`data.F2 (Fin.last (M + 1)) = 0`.

## Nonclaims

The reviewed Lean does not define an open coordinate domain, topology, measure,
or Jacobian.  It proves no two-sided local inverse, source coverage,
source/image equality, normal crossings, pole order, or RLCT extraction.
