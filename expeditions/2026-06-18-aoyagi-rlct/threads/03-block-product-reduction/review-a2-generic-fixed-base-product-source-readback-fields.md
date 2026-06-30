# Review: A2 generic fixed-base product source-readback fields

Date: 2026-06-30.

Reviewer: xhigh scout `Epicurus the 2nd`.

## Verdict

PASS, with one non-blocking Lean/API maintenance concern.

## Scope and source fidelity

The generic theorem

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
```

is scoped as pointwise fixed-base block algebra.  Its conclusion is only the
six `sourceReadback` field equalities for `A1passive`, `F2`, `A3passive`, `C`,
`Ctop`, and `F3`.  It delegates to the raw product-coordinate theorem
`sourceReadback_productCoordinate_fields_succSucc`.

The reproduction note matches this boundary: it records the prescribed
fixed-base p.13 edge shapes and then applies the raw readback theorem.

## Nonclaim boundary

No accidental overclaim was found.  The theorem has arbitrary `α`,
`CedgeBase`, `x`, and `u`; it has no theta-domain inverse, prior, image,
normal-crossing, pole-order, or RLCT conclusion.  The concrete Case 2 theorem
still concludes only the same six field equalities and keeps its nonclaim
boundary.

## Dependency placement

The new module `RegularSuspensionSourceReadback` is a reasonable dependency
boundary: it imports `RegularSuspensionCoordinates` and
`RetainedPassiveCoordinates`, then the concrete Case 2 theorem imports and
instantiates it.  The aggregator import was appended, consistent with local
policy.

## Concern

The generic proof still uses definitional unfolding and `simp` to expose the
left/middle/right product-coordinate matrix shapes.  The Case 2 theorem is now
cleaner, but if the product-coordinate matrix constructor implementation
changes, this generic proof may need small maintenance.  This is not
mathematical overreach.

## Verification

The reviewer independently ran:

```text
git diff --check
scripts/sorries
scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSourceReadback
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
```
