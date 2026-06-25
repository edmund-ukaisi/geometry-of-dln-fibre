# Review - A2 single-edge source-dependent residual-matrix family

Date: 2026-06-25.

Reviewer mode: xhigh scout review plus controller integration.

## Verdict

Pass.

## Scope Check

The intended theorem is a pointwise wrapper around the existing one-edge p.13
coordinate readout.  It allows `D` to vary with a base point `x`, but at each
point the calculation is exactly the one-edge finite block calculation:

```text
regular coordinates = u,
residual coordinates = value(Dbase x).
```

The statement does not claim source coverage, source-measure transport,
normal crossings, pole order, or RLCT.

Kepler's xhigh read-only audit agreed that the wrapper is mathematically sound
and useful at this boundary.  The source dependence is harmless because `x`
only selects the residual matrix pointwise.  The same audit warned that a
selected-entry specialization is appropriate only as a separate finite
coordinate-readout slice, not as source-chart production.

Hubble's Lean scout checked the placement and proof skeleton.  It also noted
that continuity is structurally easy in the one-edge residual-matrix case; the
landed theorem proves continuity at `(x₀,u₀)` under the global hypothesis
`Continuous Dbase`.

Focused `ChartTopology` and `RegularSuspensionCoordinates` builds passed.

## Risks To Keep Explicit

- The determinant-unit hypothesis on `Ctop(u)` remains necessary.
- The theorem should remain one-edge; multi-edge product-coordinate residuals
  are constrained by intermediate factor data.
- The continuity theorem assumes `Continuous Dbase`; it does not construct or
  verify any source-specific residual matrix family.
