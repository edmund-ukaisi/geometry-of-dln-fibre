# Statement Card - A2 retained-passive transformed-edge readbacks

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveTransformedEdge_readbacks
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks
```

## Claim

For the retained-passive transformed block

```text
M_p =
  [ A1_p       -A1_p * F2_p
    A3_p        C_p - A3_p * F2_p ],
```

the one-step chart readbacks recover the supplied coordinate blocks:

```text
topLeft(M_p) = A1_p,
upperRight(M_p) = -A1_p * F2_p,
-A1_p^-1 * upperRight(M_p) = F2_p,
lowerLeft(M_p) = A3_p,
schurResidualBlock(M_p) = C_p.
```

The inverse readback assumes `IsUnit det(A1_p)`.

The fixed-base corollary applies the same readbacks to the actual deterministic
suffix-state transformed edge because the existing fixed-base theorem identifies
that edge with `M_p`.

## Method

The direct block projections are definitional from `fromBlocks`.  The
upper-right chart readout uses

```text
-A1_p^-1 * (-(A1_p * F2_p))
  = A1_p^-1 * (A1_p * F2_p)
  = F2_p.
```

The Schur residual readout is the previously proved lemma
`schurResidualBlock_retainedPassiveTransformedEdge`.

The fixed-base theorem rewrites

```text
transformedEdge(E, p, suffixState(E,last,p+1)) = M_p
```

and then reuses the transformed-block readback theorem.

## Role

This is a finite per-edge readback lemma for the retained-passive source-map
skeleton.  It is the local algebra needed before bundling the two-sided
retained-passive coordinate inverse.

## Nonclaims

This does not construct the retained-passive coordinate domain and does not
prove a bundled two-sided inverse.  It does not prove source-rank coverage,
source/image equality, source-measure pushforward, Jacobian/prior density,
normal crossings, pole order, or RLCT extraction.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

Passed on 2026-06-26.

Full check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

also passed on 2026-06-26, with pre-existing warnings outside the touched
module.  `scripts/sorries` and `git diff --check` also passed.

Review:

```text
threads/03-block-product-reduction/review-a2-retained-passive-transformed-edge-readbacks.md
```
