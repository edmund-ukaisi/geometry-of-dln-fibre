# Reproduction - A2 with-following rank-cut original-prior local loss with prior density at product-zero

Date: 2026-07-06.

Status: proposed Lean wrapper.

## Claim

The continuous pulled-back density rank-cut local-loss theorem can be
specialized to the same edge-family density that defines the original prior:

```text
edgeDensity = priorDensity.
```

The resulting loss-density factor is therefore

```text
priorDensity(CedgeProd(E,u)).
```

This is a specialization of the density factor in the integrand only.  It does
not identify the original edge-family prior with a product-coordinate
pushforward, and it does not transport the prior through the p.13 map.

## Product-Zero Base Point

The tempting shortcut would be to use the existing continuity assumption

```text
ContinuousAt priorDensity (sourceChart z0)
```

to supply the continuity needed by the pulled-back density theorem.  That would
require

```text
CedgeProd(sourceChart z0, 0) = sourceChart z0.
```

This equality is not available, and it is not expected in general.

At `u = 0`, the p.13 product-coordinate matrix constructor has

```text
F2 = 0,  F3 = 0,  Ctop = 1.
```

Thus its raw edge matrices have the product-coordinate block forms

```text
[1 0; 0 C_p]
```

with the same transformed Schur residual factors as the base family.  The fixed
self-base edge matrices are only known to be in determinant-chart/identity
corner form; an individual edge can have an upper-right block

```text
[1 B_p; 0 D_p].
```

The existing self-base API proves determinant-chart continuity data, source
rank data, and total product identities.  It does not prove that these
upper-right blocks vanish edgewise.  Therefore continuity at `sourceChart z0`
does not by itself give continuity at the product-zero representative.

## Honest Hypotheses

Keep the original assumption

```text
ContinuousAt priorDensity (sourceChart z0)
```

because upstream residual/prior domination theorems use it for the original
prior measure.  Add the two direct density-bound hypotheses at the actual
point used by the product-coordinate density theorem:

```text
ContinuousAt priorDensity (CedgeProd(sourceChart z0, 0)),
0 < priorDensity (CedgeProd(sourceChart z0, 0)).
```

These are exactly the generic hypotheses of the existing theorem with
`edgeDensity := priorDensity`.

## Composition

Start from

```text
exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_continuousAt_pos_density
```

and instantiate:

```text
edgeDensity := priorDensity.
```

All source, rank-cut, residual zero-locus, fixed-base centering, source-data,
basis, raw Haar, and regular Haar hypotheses remain exactly as in the generic
theorem.

The final integral is over

```text
(originalEdgeFamilyPrior priorDensity).restrict (U cap rankCutSource) prod nu
```

with integrand density factor

```text
priorDensity(CedgeProd(z.1,u)).
```

The measure still uses `priorDensity` on original edge-family coordinates.
The integrand uses the same scalar function after the p.13 product-coordinate
edge-family map.  This is a local bounded-density specialization, not a
change-of-variables theorem.

## Kill Conditions

- The theorem is read as proving `CedgeProd(sourceChart z0,0) = sourceChart z0`.
- The theorem is read as deriving product-zero continuity from continuity at
  `sourceChart z0`.
- The theorem is read as proving prior transport or a product-coordinate
  change of variables for `originalEdgeFamilyPrior`.
- The theorem is read as proving residual zero-locus nullity, source-rank or
  analytic atlas coverage, normal crossings, pole order, or RLCT.

## Nonclaims

- No base-at-zero equality.
- No proof that the product-zero representative equals the source-chart base.
- No statistical prior identification or transport through `CedgeProd`.
- No determinant/raw Haar transport.
- No source-rank or analytic atlas coverage.
- No normal-crossing construction, pole-order count, or RLCT extraction.
