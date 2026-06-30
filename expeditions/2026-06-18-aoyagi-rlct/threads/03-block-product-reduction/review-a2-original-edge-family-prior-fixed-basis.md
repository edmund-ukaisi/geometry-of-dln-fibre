# Review - A2 Original Edge-Family Prior In Fixed Bases

Date: 2026-06-30.

Reviewer: xhigh sidecar `Noether the 2nd` plus controller check.

## Verdict

PASS for the fixed-basis original edge-family measure API, with a strict
nonclaim boundary.

The target is useful because it proves the map-back equality

```text
Measure.map (edgeFamilyMatrixTuple b) (originalEdgeFamilyVolume b)
  = originalTupleVolume d.
```

Without that equality, the file would only name a `Measure.map` wrapper and
would not move the source-prior frontier.

## Checks

The fixed-basis maps are the expected ones:

```text
edgeFamilyMatrixTuple b E
  = chainMapMatrixTuple b (fun p => (E p : _ ->ₗ[ℝ] _))

tupleToEdgeFamily b A p
  = LinearMap.toContinuousLinearMap
      (Matrix.toLin (b p.castSucc) (b p.succ) (A p)).
```

The two inverse lemmas reduce edgewise to the matrix/linear-map basis inverse
facts.  The continuity lemmas use the existing fixed-basis coordinate
continuity theorems from `ChartTopology.lean`.

The measure theorem uses `Measure.map_map`, then replaces
`edgeFamilyMatrixTuple b ∘ tupleToEdgeFamily b` by `id` via
`Measure.map_congr`.  This is the right direction for later use: the
edge-family measure is not defined by an Aoyagi chart, but its matrix
coordinates recover the original tuple measure.

## Frontier

This file supplies the source-side original measure object for continuous edge
families.  The remaining hard step is still a local comparison between this
measure, restricted to a chart image or chart piece, and the retained-passive
chart-produced source-image measure.  The existing consumer sockets are still
the chart-piece equality and readback-domination theorems in
`RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean`.

## Nonclaims

No theorem here identifies `originalEdgeFamilyVolume` or
`originalEdgeFamilyPrior` with an Aoyagi chart-produced measure.  No theorem
proves source-image equality, readback domination, source-rank coverage,
Haar/Jacobian transport, normal crossings, pole order, or RLCT extraction.
