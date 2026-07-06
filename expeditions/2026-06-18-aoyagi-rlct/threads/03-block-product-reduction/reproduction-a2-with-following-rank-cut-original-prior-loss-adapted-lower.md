# Reproduction - A2 with-following rank-cut original-prior local loss with produced adapted lower bound

Date: 2026-07-06.

Status: Lean proved as a conditional wrapper.

## Claim

On the with-following Case 2 rank-cut p.13/readback source patch, the
adapted-product lower-bound input in the previous local original-loss handoff
can be produced from the fixed-base p.13 product-coordinate lower-bound theorem,
provided the edge-family base point is aligned with the fixed reverse-edge
base family.

This removes only the adapted-product lower-bound hypothesis.  The residual
zero-locus-nullity, fixed-base source data, endpoint bases, regular-coordinate
Haar measure, and regular-coordinate density bounds remain explicit.

## Setup

The previous local original-loss handoff returns an open theta neighborhood
`V` and the rank-cut source

```text
rankCutSource =
  (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

Its continuation requires, among other hypotheses, a radius `R`, a positive
constant `c`, and the local lower bound

```text
eventually E near sourceChart z0 within rankCutSource,
  for all u in ball(0,R),
    c * (residualSq(E) + regularSq(u))
      <= adaptedProductDifferenceSquareSum(E,u).
```

The fixed-base p.13 product-coordinate theorem gives the same form of lower
bound on the full source stratum:

```text
eventually E near sourceChart z0 within sourceStratum,
  for all u in ball(0,R),
    c * (residualSq(E) + regularSq(u))
      <= adaptedProductDifferenceSquareSum(E,u).
```

It also chooses `R` and `c` with

```text
0 < R,  R <= Rmax,  0 < c.
```

## Base Alignment

The p.13 product-coordinate lower-bound theorem is a fixed-base theorem.  Its
base family is

```text
fun p => LinearMap.toContinuousLinearMap (reverseEdge W2 B2 p).
```

In the rank-cut handoff the base edge map is the identity on edge families:

```text
CedgeBase = fun E => E,
x0 = sourceChart z0.
```

Therefore the lower-bound theorem needs the explicit centering hypothesis

```text
sourceChart z0 =
  fun p => LinearMap.toContinuousLinearMap (reverseEdge W2 B2 p).
```

The identity edge-family map is continuous at `sourceChart z0`, so no separate
continuity hypothesis is needed.

## Restriction To The Rank Cut

Since

```text
rankCutSource =
  (p13SourceSet cap readback^{-1}(V)) cap sourceStratum,
```

we have

```text
rankCutSource subset sourceStratum.
```

The eventual lower bound over `nhdsWithin (sourceChart z0) sourceStratum`
therefore restricts to an eventual lower bound over
`nhdsWithin (sourceChart z0) rankCutSource`.

This is purely filter monotonicity:

```text
nhdsWithin x rankCutSource <= nhdsWithin x sourceStratum.
```

## Resulting Continuation

Given:

- residual zero-locus nullity for `originalEdgeFamilyPrior.restrict rankCutSource`;
- a raw-coordinate Haar measure and its additive Haar instance, used only to
  instantiate the upstream residual-source continuation;
- `sourceData` at `sourceChart z0` with base map `fun E => E`;
- the base-alignment equality above;
- endpoint bases `b`;
- a regular-coordinate Haar measure `nu`;
- a positive radius cap `Rmax`;

the wrapper chooses `R` and `c` with `0 < R`, `R <= Rmax`, and `0 < c`.
For that chosen `R`, if the regular-coordinate density is locally nonnegative
and locally bounded above by `C` on the larger cap
`rankCutSource x ball(0,Rmax)`, then the bound restricts to
`rankCutSource x ball(0,R)` because `R <= Rmax`.  The
previous local original-loss handoff gives an open edge-family neighborhood
`U` of `sourceChart z0` and a finite lower integral of the original `lossDLN`
over

```text
(originalEdgeFamilyPrior.restrict (U cap rankCutSource)).prod nu.
```

## Lean Target

Implemented in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorLossRankCutBridge.lean
```

with theorem:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_density_bounds
```

The proof:

- reuses the previous rank-cut local original-loss handoff;
- proves continuity of `fun E => E` at `sourceChart z0` internally;
- assumes the fixed-base equality `sourceChart z0 = reverseEdge`;
- calls the self-base p.13 adapted-product lower-bound theorem to choose
  `R` and `c`;
- restricts the eventual source-stratum lower bound to the rank-cut source;
- restricts density bounds from the cap `Rmax` to the produced radius `R`.

Focused `lake env lean` and focused module build passed before this note was
marked proved.  Full-library and axiom-clean verification are recorded in the
claim ledger once run.

## Kill Conditions

- The theorem is read as proving residual zero-locus nullity.
- The theorem is read as proving the base-alignment equality
  `sourceChart z0 = reverseEdge`.
- The theorem is read as proving density nonnegativity or an upper density
  bound.
- The theorem is read as identifying or transporting the statistical prior.
- The theorem is read as proving source-rank coverage, analytic atlas
  coverage, normal crossings, pole order, or RLCT.

## Nonclaims

- No residual zero-locus-nullity proof.
- No proof that `sourceChart z0` is the fixed reverse-edge base family.
- No density comparison or full prior transport.
- No determinant/raw Haar transport.
- No source-rank or analytic atlas coverage.
- No normal crossings, pole order, or RLCT extraction.
