# Review - A2 one-step determinant-chart coordinate equivalence

Date: 2026-06-24.

Reviewer: xhigh explorer `Herschel the 4th`.

Status: passed for the mathematics; Lean target staged downstream in
`ChartTopology.lean`.

## Reviewed Shape

The reviewer checked the reproduction and statement card against the existing
one-step coordinate definitions in `ProductReduction.lean`.

No sign, inverse, or domain errors were found.  The reviewed forward map is

```text
Ctop = C1 * A1,
F2   = -(A1^{-1} * A2),
F3   = F3_old - D * A3 * (C1 * A1)^{-1},
C    = A4 - A3 * A1^{-1} * A2.
```

The reviewed inverse map is

```text
C1     = Ctop * A1^{-1},
F3_old = F3 + D * A3 * Ctop^{-1},
A2     = -A1 * F2,
A4     = C - A3 * F2.
```

The sign in `A4` is correct because `F2 = -A1^{-1} * A2`, and no inverse of
the passive residual block `D` appears.

## Domain Check

The raw determinant chart is

```text
IsUnit det(C1) and IsUnit det(A1).
```

The chart determinant domain is

```text
IsUnit det(Ctop) and IsUnit det(A1).
```

For the existing right-inverse theorem, the reviewer noted that Lean's
argument order is `hA1` then `hCtop`, while chart `detChart` stores the pair
as `(hCtop, hA1)`.  The implementation must therefore pass `hy.2.2` before
`hy.2.1`.

## Implementation Guidance

The bundled homeomorphism is the correct mathematical target, but it should be
staged after continuity lemmas for the determinant-chart subtype maps.  Since
matrix-inversion continuity lives in `ChartTopology.lean` and that file is
downstream of `ProductReduction.lean`, the topological theorem belongs in
`ChartTopology.lean` or a new downstream topology file, not in
`ProductReduction.lean`.

## Nonclaims

No analytic regularity, no analytic Jacobian determinant calculation, no
source-rank openness, no source coverage, no ideal-germ transport, no
regular-suspension certificate, no normal crossings, no pole-order theorem,
no RLCT extraction, no inversion of `D`, and no identification of the
synthetic shifted reduced certificate with the actual full product-difference
certificate.

