# Review - A2 Case 2 passive-theta endpoint reference

Date: 2026-07-01.

Status: controller review PASS; xhigh pen-and-paper/source scout `Einstein
the 3rd` and xhigh Lean/API scout `Banach the 3rd` confirm the coordinate
boundary.

## Checks

- The reference measure includes all passive fields:
  `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.
- The center measure is the existing selected-entry weighted signed-box
  measure, not an unweighted box.
- The implementation avoids bare `volume` on the nested passive product,
  because a direct probe showed a measurable-space mismatch with the default
  product/Pi measurable space.
- The support theorem requires `Omega subset case2PassiveThetaDetSector`.
  It does not claim determinant-sector membership for arbitrary local sets.
- The proof uses continuity of `Y` only to discharge a.e.-measurability for
  the existing generic support theorem.
- The theorem name says `referenceSource` and `restrict_detChartSet_eq_self`;
  it does not say Haar transport or domination.
- The named image measure is definitionally the endpoint pushforward of the
  concrete reference source restricted to the local set.  It is not a new Haar
  measure.
- The passive-measure domination theorem targets this named image measure.  It
  does not introduce any determinant-chart Haar measure.
- The Lean/API scout identified the hard obstruction to unrestricted full
  determinant-chart Haar domination: `TopologyTuple` has a full `C` family,
  while `Case2PassiveTheta` fills that family from selected-entry residual
  data.  The reference pushforward is therefore supported on an image slice of
  the determinant chart.

## Boundary

This is not the missing endpoint image-measure theorem.  In particular, it
does not prove

```text
Measure.map Y (referenceSource.restrict V)
  <= c • rawHaar.restrict topologyTupleDetChartSet.
```

That unrestricted full-Haar target is obstructed for the current theta domain.
The next frontier is either to enlarge the theta source with the missing full
`C` coordinates, or to formulate the correct selected-entry/chart-image target
measure and push that through the downstream sockets.
