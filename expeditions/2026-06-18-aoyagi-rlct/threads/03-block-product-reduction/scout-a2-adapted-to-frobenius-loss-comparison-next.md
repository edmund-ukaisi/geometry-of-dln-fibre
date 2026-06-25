# Scout - A2 adapted product-difference to Frobenius loss comparison

Date: 2026-06-25.

Scout: xhigh `Hume the 5th`, read-only.

## Recommendation

After the adapted-loss finite-integral front end, the next substantive A2
target is not another integrability wrapper.  It is the actual finite
comparison behind the remaining hypothesis

```text
c0 * paperEndpointFixedBaseAdaptedProductDifferenceSquareSum ... <= loss.
```

The first target should be an endpoint/Frobenius-square loss comparison, not a
statistical/KL comparison.

## Places To Inspect

- `RegularSuspensionCoordinates.lean`, around the fixed-base adapted
  product-difference definitions and comparisons;
- `RegularSuspensionLocalMeasure.lean`, where the new comparison hypothesis is
  consumed;
- `RlctPayoff.lean`, for `lossDLN`, only as a definition and not as a source
  theorem from the quiver project.

## Pen-And-Paper Requirement

Before Lean, reproduce the finite-dimensional comparison precisely:

1. identify the endpoint product matrix represented by the adapted fixed-base
   coordinate map;
2. identify the square-Frobenius endpoint loss to compare against;
3. check source/target orientation and `reverseEdge` product conventions;
4. decide whether the theorem is only an endpoint matrix Frobenius comparison
   or genuinely a `lossDLN` comparison through a formal tuple/chart map;
5. account for basis changes by explicit finite-dimensional norm equivalence;
6. keep statistical/KL loss outside the theorem unless covariance/noise lower
   bounds are supplied.

## Overclaiming Boundary

Do not state a direct `lossDLN` comparison without a formal map from the p.13
product-coordinate object to the network tuple used by `lossDLN`.  Do not
claim source-rank openness, product chart construction, Jacobian/density
transport, normal crossings, pole order, or RLCT.

