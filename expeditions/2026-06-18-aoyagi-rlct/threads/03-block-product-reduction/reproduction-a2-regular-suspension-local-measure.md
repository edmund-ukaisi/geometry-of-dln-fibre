# Reproduction - A2 regular-suspension local measure handoff

Date: 2026-06-25.

Status: small source-to-measure handoff formalised in Lean.

## Source facts

The p.13 fixed-base regular-coordinate source package already proves
source-rank relative-neighborhood facts.  The two used here are:

```text
literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source
const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source
```

The first says that, on the `nhdsWithin` filter of the fixed-base source rank
stratum,

```text
(1/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= literalProductDifferenceSquareSum(x).
```

The second says that if `0 <= c` and a supplied base loss has a local lower
bound

```text
c * literalProductDifferenceSquareSum(x) <= loss(x)
```

on the same source-rank filter, then

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x)) <= loss(x)
```

on that filter.  This is only the finite p.13 comparison; the supplied lower
bound is still where any original DLN loss comparison would have to enter.

## Measure handoff

Let

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

Assume `S` is measurable.  Applying

```text
exists_open_ae_restrict_inter_of_eventually_nhdsWithin
```

to either source-filter fact gives an open neighborhood `U` of the base point
such that the same inequality holds for almost every `x` with respect to

```text
mu.restrict (U inter S).
```

For an auxiliary measurable coordinate space with measure `nu`, applying

```text
exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
```

gives the first-projection product version: the same base inequality holds for
almost every `z` with respect to

```text
(mu.restrict (U inter S)).prod nu
```

after replacing `x` by `z.1`.

## Uniform Product-Hypothesis Handoff

There is one further elementary use of the same principle.  Suppose the source
filter already supplies bounds uniformly for every p.13 regular-coordinate
fiber point `u` in a ball:

```text
forall eventually x in nhdsWithin x0 S,
  forall u in ball(0,R),
    c * (residualSquareSum(x) + regularSquareSum(u)) <= loss(x,u),

forall eventually x in nhdsWithin x0 S,
  forall u in ball(0,R), 0 <= density(x,u),

forall eventually x in nhdsWithin x0 S,
  forall u in ball(0,R), density(x,u) <= C.
```

After intersecting these three eventual facts, apply the product version of
the local-measure handoff to the base predicate

```text
P(x) := all three forall-u bounds hold at x.
```

The result is one open neighborhood `U` such that the three product-measure
a.e. hypotheses hold over

```text
(mu.restrict (U inter S)).prod nu.
```

This is exactly the shape of the loss and density inputs expected by the
finite-side p.13 regular-coordinate adapter.  It still does not prove the
uniform source-filter bounds themselves, and it does not address the residual
positivity or residual negative-power integral inputs of that adapter.

## Finite-Integral Bridge

The final wrapper in this file now composes the uniform product-hypothesis
handoff with the p.13 finite-side adapter from
`RegularSuspensionSquareSumIntegrability.lean`.

In addition to the source-filter uniform loss/density bounds above, assume:

```text
0 < residualSquareSum(x)  a.e. for mu.restrict S,
int^- x, ofReal(residualSquareSum(x)^(-t)) d(mu.restrict S) < infinity,
R > 0, c > 0, C >= 0, t > 0.
```

After the local-measure handoff gives `U`, the proof restricts the two residual
base hypotheses from `S` to `U inter S` by measure monotonicity.  The existing
p.13 finite-side adapter then gives:

```text
int^- (x,u) over (mu.restrict (U inter S)).prod nu,
  ofReal(1_{ball(0,R)}(u) * loss(x,u)^(-(t + regularCount/2)) * density(x,u))
  < infinity.
```

This is a bridge between already-supplied local source/filter hypotheses and
the already-proved finite-side theorem.  It is not a source proof of residual
positivity or residual integrability.

## Boundary

The first product statements are deliberately first-coordinate statements.
They do not identify the auxiliary product fiber with Aoyagi's regular
coordinates and do not derive an inequality involving `regularSquareSum(u)`
for a product fiber coordinate `u`.  The uniform-in-fiber theorem has that
shape only because the corresponding `forall u` loss/density bounds are
supplied on the source filter.

Still missing:

- measurable-source-stratum proof;
- p.13 analytic product chart;
- source/product coordinate identification;
- original DLN loss comparison;
- density/Jacobian transport;
- proof of residual positivity and residual negative-power integrability;
- endpoint/divergence, threshold equality, normal crossings, pole order, and
  RLCT extraction.

## Lean Shape

Lean proves this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_literal_regular_add_residual_squareSum_half_le
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_fst_const_mul_literal_squareSum_le_loss_to_half_regular_add_residual_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
```
