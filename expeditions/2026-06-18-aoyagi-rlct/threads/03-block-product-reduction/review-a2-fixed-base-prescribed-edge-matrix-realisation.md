# Review - A2 fixed-base prescribed edge-matrix realisation

Date: 2026-06-25.

## Verdict

Passed at the pointwise fixed-base matrix-realisation scope.

## Checks

The algebraic realisation is exactly the Mathlib inverse law:

```text
LinearMap.toMatrix b_source b_target (Matrix.toLin b_source b_target G) = G.
```

The continuous realisation uses `LinearMap.toContinuousLinearMap`; its coercion
back to a linear map is definitional, so the same fixed-base matrix readout
applies.

The coordinate theorem first proves the realised edge matrix family equals the
prescribed matrix family `G`, then delegates to the already-checked
product-family coordinate readout.  The residual coordinate remains
`residualProduct G last 0`.

## Residual Risk

The theorem is pointwise.  The next real frontier is to define a
product-coordinate matrix family `G(x,u)` and prove its transformed-edge
block-shape hypotheses and coordinate identities.  A fully parameterized
wrapper should not unfold the large coordinate-map definition casually; an
attempted convenience wrapper was removed after it caused slow elaboration.
