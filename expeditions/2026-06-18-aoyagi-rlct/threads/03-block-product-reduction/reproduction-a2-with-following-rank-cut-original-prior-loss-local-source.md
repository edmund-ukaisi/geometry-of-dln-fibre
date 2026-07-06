# Reproduction - A2 with-following rank-cut original-prior local original-loss handoff

Date: 2026-07-06.

Status: Lean proved as a conditional wrapper.

## Claim

On the with-following Case 2 rank-cut p.13/readback source patch, the existing
rank-cut residual-source theorem supplies exactly the residual inputs required
by the local-source original `lossDLN` finite-integral socket.  Therefore, once
the remaining local loss-side hypotheses are supplied explicitly, the original
edge-family prior gives a finite regular-coordinate integral of the original
square-Frobenius loss over a further open edge-family neighborhood.

This is not a proof of any remaining loss-side hypothesis.  The residual
zero-locus-nullity, adapted-product lower bound, density bounds, and fixed-base
source-data alignment remain explicit inputs.

## Setup

The previous rank-cut theorem returns an open theta neighborhood `V` and

```text
rankCutSource =
  (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

It also returns, for the original edge-family prior

```text
muPrior =
  originalEdgeFamilyPrior
    (paperEndpointFixedBaseFinBasis W2 B2 U0 hU0)
    priorDensity,
```

the conditional residual-source package

```text
zero locus of residualSq has muPrior.restrict rankCutSource measure zero
  ->
    (residualSq is positive a.e. for muPrior.restrict rankCutSource)
    and
    residualNegPowerIntegrableOn (fun E => E) rankCutSource muPrior t.
```

The local-source original-loss theorem requires:

- a `PaperEndpointFixedBaseRegularCoordinateSourceData` object at the edge
  base point `sourceChart z0`, with base map `fun E => E`;
- an endpoint basis `b` for writing the chain-map tuple and target matrix;
- an additive Haar measure `nu` on the regular-coordinate Euclidean space;
- a regular-coordinate product density `lossDensity`;
- positive constants `R` and `c`, a finite upper bound `C`, and `0 < t`;
- measurability of the local source;
- residual a.e. positivity and residual negative-power integrability on that
  local source;
- a local lower bound from residual-plus-regular square-sum to the adapted
  p.13 product-difference square-sum;
- local nonnegativity and upper bounds for `lossDensity`.

The rank-cut theorem already returns measurability of `rankCutSource`.  The
new residual-source theorem supplies the two residual hypotheses after the
zero-locus-nullity input.  All other bullets remain explicit inputs.

## Calculation

Fix the returned `V` and write

```text
source = rankCutSource.
```

Assume the zero-locus-nullity hypothesis on `muPrior.restrict source`.  The
rank-cut residual-source theorem gives

```text
hpos_source :
  forall ae E with respect to muPrior.restrict source,
    0 < residualSq(E),

hbase_source :
  residualNegPowerIntegrableOn (fun E => E) source muPrior t.
```

The local-source original-loss theorem is then applied with

```text
alpha      = EdgeFamily,
x0         = sourceChart z0,
CedgeBase  = fun E => E,
source     = rankCutSource,
mu         = muPrior,
CedgeProd  = paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
               W2 B2 U0 hU0 (fun E => E).
```

Its conclusion is an open edge-family neighborhood `U` of `sourceChart z0` and
a finite lower integral

```text
integral over (muPrior.restrict (U cap rankCutSource)).prod nu
  of
    indicator(ball(0,R)) *
    ofReal((lossDLN target chainTuple)^(-(t + regularCount/2))
           * lossDensity).
```

The theorem is local in the edge-family source coordinates.  It does not yet
identify the product density with Aoyagi's statistical prior in full
coordinates and it does not prove the adapted-product lower bound or the
zero-locus-nullity input.

## Lean Target

Implemented in the downstream file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorLossRankCutBridge.lean
```

The theorem name should state the content:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_lossDLN_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_zero_set_null_of_localSource_bounds
```

The theorem should return the same local `V` data as the residual-source
rank-cut theorem, plus a continuation:

```text
zero-locus nullity on rankCutSource
  -> sourceData, endpoint bases, regular Haar, local adapted bound,
     local density bounds
  -> finite original-loss lower integral over
     (muPrior.restrict (U cap rankCutSource)).prod nu.
```

Lean implementation notes:

- the endpoint dimension function `d` and basis family `b` are explicit inputs
  to the continuation;
- the target matrix in the displayed integral is
  `LinearMap.toMatrix (b 0) (b (Fin.last 2))` of the fixed endpoint
  `chainMap`;
- the chain tuple is `chainMapMatrixTuple b` applied to the p.13 regular
  product-coordinate edge family;
- the proof repackages the rank-cut source theorem's field-expanded
  left-inverse and rank-stratum facts before passing its residual source
  hypotheses to the existing local-source original-loss socket.

Verification passed for the focused Lean file, focused module build,
`lake env lean DLNFibre.lean`, full local `lake build DLNFibre`,
`scripts/sorries`, `git diff --check`, touched-file marker scan, and a direct
axiom probe.  The new theorem reports only
`[propext, Classical.choice, Quot.sound]`.

## Kill Conditions

- The theorem is read as proving residual zero-locus nullity.
- The theorem is read as proving the adapted-product lower bound or density
  bounds.
- The theorem is read as identifying the full original statistical prior with
  the displayed product measure.
- The theorem is read as proving source-rank coverage, analytic atlas
  coverage, normal crossings, pole order, or RLCT.

## Nonclaims

- No zero-locus-nullity proof.
- No adapted-product lower-bound proof.
- No density comparison or full prior transport.
- No source-rank or analytic atlas coverage.
- No determinant/raw Haar transport or Jacobian normalization.
- No normal crossings, pole order, or RLCT extraction.
