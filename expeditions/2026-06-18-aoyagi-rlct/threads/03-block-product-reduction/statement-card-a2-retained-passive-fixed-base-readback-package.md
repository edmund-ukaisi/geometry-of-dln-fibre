# Statement Card - A2 retained-passive fixed-base readback package

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Name

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointAndEdgeReadbacks_eq_targets
```

## Reproduction

```text
reproduction-a2-retained-passive-fixed-base-readback-package.md
```

## Claim

Under the same solved-endpoint hypotheses as the active endpoint package,
retained-passive fixed-base edges read back the active source-left fields and
the per-edge transformed-edge coordinate blocks.

For the source-left suffix state `S_0`, Lean proves

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3.
```

For every edge `p`, with

```text
T_p = transformedEdge(E,p,S_{p+1}),
```

Lean proves

```text
topLeft(T_p) = A1_p,
upperRight(T_p) = -A1_p * F2_p,
-(A1_p^-1 * upperRight(T_p)) = F2_p,
lowerLeft(T_p) = A3_p,
schurResidualBlock(T_p) = C_p.
```

## Method

The proof reuses
`retainedPassiveFixedBaseEdgeMatrix_activeEndpointFields_eq_targets` for the
three active source-left fields.  It derives the full determinant-unit `A1`
family from the passive unit hypotheses, `det(Ctop)` unit, and the solved
`A1_0=Tail^-1*Ctop` equation.  Then it applies
`retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks` at each edge.

## Role

This is the finite fixed-base readback package immediately before a bundled
retained-passive coordinate-domain or local inverse object.  It combines
source-left endpoint readbacks with per-edge transformed-edge coordinate
readbacks.

## Nonclaims

No bundled retained-passive coordinate-domain structure is defined.  No
two-sided local inverse, source-rank coverage, source/image equality, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26.

Full check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

also passed on 2026-06-26, with pre-existing warnings outside the touched
module.  `scripts/sorries` and `git diff --check` also passed.

Review:

```text
threads/03-block-product-reduction/review-a2-retained-passive-fixed-base-readback-package.md
```
