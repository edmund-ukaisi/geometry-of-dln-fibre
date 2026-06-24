# Reproduction - A2 regular-suspension coordinate map source data

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 displays the post-product-reduction coordinates in four
families:

```text
C1 - Er,   F2,   F3,   product C^(s).
```

In the fixed-base Lean suffix-state convention already reproduced in earlier
A2 slices, the first three families are represented by

```text
S.Ctop - 1,   -S.B,   lowerLeftBlock S.L,
```

and the reduced residual block is represented by `S.D`.

## Calculation

The existing scalar source-data package says that, at the base point `x0`, each
scalar coordinate in the regular families vanishes and is continuous at `x0`.
The same statement has already been reproduced separately for the residual
`D` block and for the combined cleaned product-difference coordinate index.

This slice performs only the elementary product-topology repackaging.  Define
the Pi-valued maps

```text
x |-> (c |-> value (S(x).Ctop - 1) (-(S(x).B)) (lowerLeftBlock S(x).L) c),
x |-> (c |-> value (S(x).D) c),
x |-> (c |-> value (S(x).Ctop - 1) (-(S(x).B)) (lowerLeftBlock S(x).L) (S(x).D) c).
```

For each map, the value at `x0` is the zero function because every scalar
coordinate is zero at `x0`.  Continuity at `x0` follows componentwise from the
existing scalar centered-continuity fields and the product-topology criterion
for Pi types.

## Lean Boundary

The Lean statements are:

```text
paperEndpointFixedBaseRegularBlockCoordinateMap
paperEndpointFixedBaseResidualBlockCoordinateMap
paperEndpointFixedBaseProductDifferenceCoordinateMap
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt
```

## Nonclaims

- No analytic coordinate chart.
- No local inverse or coordinate-source rank theorem.
- No analytic germ-ideal transport.
- No chart coverage or Jacobian/prior compatibility.
- No normal-crossing construction, pole order, or RLCT extraction.
