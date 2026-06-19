# A4 Case 1(1) Selected-Old Unit Chart-Family Boundary

Status: reproduced a narrow supplied chart-family/principalization boundary.

## Source Situation

In Aoyagi Case 1(1), the selected chart denominator is the old exceptional
variable `u_(s0,k0)` itself.  In the Lean finite center this selected old
generator is represented by the token

```text
Sum.inl () : Case1CenterGenerator.
```

The token alone does not determine `(s0,k0)`.  The selected label and first
jump data must still come from the existing Case 1 selected-old boundary.

## Boundary Data

Combine two already supplied pieces:

```text
lowered recurrence boundary:
  first-jump data, same-domain exponent update,
  supplied pre/post recurrence weights for the level move J+J1 -> J;

Case 1 center chart-family boundary:
  chart regularity and transition regularity predicates for every finite
  center generator.
```

The new boundary only packages these together for the selected-old `Unit`
chart.

## Finite Principalization

For the selected-old chart token, the finite selected-entry substitution map
sends the selected generator to the chart variable `u`.  Therefore:

```text
u belongs to the transformed finite center value set,
u divides every transformed finite center generator,
Ideal(transformed finite center generators) = (u).
```

This is finite ideal algebra for the center generators.  It does not prove an
affine atlas or chart coverage.

## Projections

The boundary should project:

- selected introducedness and selected level from the lowered recurrence
  boundary;
- selected-old center membership;
- supplied chart regularity for the selected-old chart token;
- supplied transition regularity from/to the selected-old chart token and any
  finite center generator;
- selected-old finite center value/divisibility/principalization facts;
- the supplied pre/post recurrence-weight source identities;
- the same-domain exponent-certificate update.

## Caveats

- The scalar `u` is the selected old denominator `u_(s0,k0)`, not the
  displayed Case 1(2) pivot `u_(S,J+1)`.
- The `Unit` token is finite center bookkeeping only; it does not identify the
  hidden old label without the carried selected-label data.
- No chart construction, atlas coverage, regularity proof from coordinates,
  Jacobian, `Q/P`, normal crossings, RLCT extraction, or full transition
  invariant is proved.
