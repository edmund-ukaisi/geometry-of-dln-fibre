# Review - A2 selected-entry local-source finite-integral handoff

Date: 2026-06-25.

## Verdict

Accepted at the stated scope.

The theorem is a nontrivial consumer of the selected-entry monomial-unit data:
it removes the generic residual-unit, density-unit, source-density bound, and
coordinatewise critical-exponent hypotheses from the local-source
finite-integral socket for the concrete selected-entry center coordinates.

## Checks

The residual model is not asserted for the source chart by definition.  It is
an explicit hypothesis:

```text
squareResidual(sourceChart y)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

This prevents the theorem from pretending that a selected-entry chart has
already been constructed inside the fixed-base source.

The weighted pushforward is also explicit:

```text
μ.restrict source
  = map sourceChart
      (signedBox.withDensity
        (ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot))).
```

Thus no measure transport, analytic Jacobian, or actual source-density theorem
is being smuggled in.

The threshold condition is correctly reduced.  For the pivot coordinate,
`k = 1` and `h = (center.erase pivot).card`, giving

```text
2 * t < (center.erase pivot).card + 1.
```

For every non-pivot coordinate, `k = h = 0`, so the condition is `0 < 1`.

## Risk Notes

The theorem is still a handoff, not source production.  It should be consumed
only after a future chart/source package proves the source chart, source image,
weighted pushforward, and residual-coordinate identity.  It is useful because
that future package no longer has to restate the selected-entry monomial-unit
calculation.
