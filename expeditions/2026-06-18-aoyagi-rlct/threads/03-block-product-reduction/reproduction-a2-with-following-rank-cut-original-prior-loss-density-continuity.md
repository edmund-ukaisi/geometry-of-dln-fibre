# Reproduction - A2 with-following rank-cut original-prior local loss with continuous density bounds

Date: 2026-07-06.

Status: Lean proved as a conditional wrapper.

## Claim

On the with-following Case 2 rank-cut p.13/readback source patch, the explicit
regular-coordinate density nonnegativity and upper-bound hypotheses in the
rank-cut original-prior local-loss handoff can be replaced by continuity and
positivity of an edge-family density after pullback along the fixed-base p.13
product-coordinate map.

This removes only the local density-bound hypotheses.  Residual zero-locus
nullity, fixed-base centering, fixed-base source data, endpoint bases,
raw-coordinate Haar, regular-coordinate Haar, source/prior transport,
source-rank or analytic atlas coverage, normal crossings, pole order, and RLCT
remain outside the theorem.

## Setup

The current adapted-lower wrapper returns an open theta-side neighborhood `V`
and the rank-cut source

```text
rankCutSource =
  (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

Its continuation assumes:

```text
0 < Rmax
sourceChart z0 = reverseEdgeBase
```

and then chooses `R` and `c` with

```text
0 < R,  R <= Rmax,  0 < c.
```

For the chosen `R`, it consumes density bounds supplied on the larger cap:

```text
eventually E near sourceChart z0 within rankCutSource,
  for all u in ball(0,Rmax),
    0 <= lossDensity(E,u),

eventually E near sourceChart z0 within rankCutSource,
  for all u in ball(0,Rmax),
    lossDensity(E,u) <= C.
```

The intended density in this wrapper is not an arbitrary density on
`EdgeFamily x regularCoordinates`.  It is an edge-family density pulled back
through the p.13 product-coordinate edge-family map:

```text
lossDensity(E,u) = edgeDensity(CedgeProd(E,u)).
```

Here

```text
CedgeProd =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    W2 B2 U0 hU0 (fun E => E).
```

## Density Bound Derivation

Assume

```text
ContinuousAt edgeDensity (CedgeProd(sourceChart z0, 0)),
0 < edgeDensity (CedgeProd(sourceChart z0, 0)).
```

The fixed-base p.13 product-coordinate map is continuous at `(sourceChart z0,0)`
because:

1. the base map `fun E => E` is continuous at `sourceChart z0`;
2. the explicit centering equality identifies

   ```text
   sourceChart z0 =
     fun p => LinearMap.toContinuousLinearMap (reverseEdge W2 B2 p);
   ```

3. the existing self-base product-coordinate continuity theorem applies.

Therefore the composed density

```text
(E,u) |-> edgeDensity(CedgeProd(E,u))
```

is continuous at `(sourceChart z0,0)` and positive there.

The local density-bound lemma then gives, for any positive cap `RdenCap`,
numbers `Rden` and `Cden` such that

```text
0 < Rden,  Rden <= RdenCap,  0 <= Cden,
```

and, eventually within `rankCutSource`,

```text
for all u in ball(0,Rden),
  0 <= edgeDensity(CedgeProd(E,u)),

for all u in ball(0,Rden),
  edgeDensity(CedgeProd(E,u)) <= Cden.
```

For the final theorem with an externally supplied cap `Rmax`, take
`RdenCap = Rmax`.

## Composition With The Adapted-Lower Wrapper

The adapted-lower wrapper itself chooses the final radius.  To combine the two
radius choices without exposing an extra shrink to the caller:

1. Use the density-continuity helper with cap `Rmax`.  It returns
   `Rden <= Rmax` and a bound `Cden`.
2. Call the adapted-lower wrapper with cap `Rden`.  It returns the final
   radius `R` and adapted constant `c` with

   ```text
   0 < R,  R <= Rden,  0 < c.
   ```

3. The density bounds produced on `ball(0,Rden)` are exactly the hypotheses
   required by the adapted-lower wrapper at its cap.
4. The final theorem reports `R <= Rmax` by transitivity:

   ```text
   R <= Rden <= Rmax.
   ```

The resulting finite integral uses the composed density:

```text
int^- z : EdgeFamily x regularCoordinates,
  1_{ball(0,R)}(u)
  * lossDLN(... CedgeProd(E,u) ...)^(-(t + regularCount/2))
  * edgeDensity(CedgeProd(E,u))
```

over

```text
(originalEdgeFamilyPrior.restrict (U cap rankCutSource)).prod nu.
```

The measure remains the original edge-family prior restricted to the rank-cut
source.  This step does not identify that prior as a product-coordinate
pushforward or prove any change-of-variables formula.

## Lean Target

The downstream theorem should live in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorLossRankCutBridge.lean
```

and should call:

```text
exists_pos_radius_le_eventually_nhdsWithin_density_comp_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_bounds_of_continuousAt_pos
```

from `OriginalLossLocalMeasure.lean`, then call:

```text
exists_open_radius_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_source_base_of_density_bounds
```

from the same rank-cut bridge file.

The density helper should be instantiated with:

```text
alpha = EdgeFamily
x0 = sourceChart z0
source = rankCutSource
CedgeBase = fun E => E
density = edgeDensity
Rmax = caller's Rmax
```

The adapted-lower wrapper should then be called with `Rmax := Rden` and
`lossDensity := fun z => edgeDensity(CedgeProd z)`.

## Kill Conditions

- The theorem is read as proving residual zero-locus nullity.
- The theorem is read as proving the fixed-base centering equality.
- The theorem is read as proving that the original statistical prior is the
  product-coordinate measure.
- The theorem is read as proving a change-of-variables formula or density
  comparison for `originalEdgeFamilyPrior`.
- The theorem is read as proving source-rank coverage, analytic atlas
  coverage, normal crossings, pole order, or RLCT.

## Nonclaims

- No residual zero-locus-nullity proof.
- No proof that `sourceChart z0` is the fixed reverse-edge base family.
- No statistical prior identification or source/prior transport.
- No determinant/raw Haar transport.
- No source-rank or analytic atlas coverage.
- No normal-crossing construction, pole-order count, or RLCT extraction.
