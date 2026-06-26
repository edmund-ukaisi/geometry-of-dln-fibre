# Statement Card - A2 retained-passive active endpoint package

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Name

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointFields_eq_targets
```

## Reproduction

```text
reproduction-a2-retained-passive-active-endpoint-package.md
```

## Claim

For a nonempty retained-passive fixed-base edge family built from full block
families `A1`, `F2`, `A3`, and `C`, assume:

```text
F2_last = 0,
det(Ctop) is a unit,
det(A1_p) is a unit for p != 0,
A1_0 = Tail^-1 * Ctop,
A3_last = -(F3 - EarlyTail) * Ctop_last.
```

Here `Tail=A1_last*...*A1_1`, `EarlyTail` is the source product tail with
`A3_last` zeroed, and `Ctop_last` is the residual top-left product at the final
edge.

Lean proves, for the source-left suffix state `S_0` of the constructed
fixed-base edge family:

```text
-S_0.B = F2_0,
S_0.Ctop = Ctop,
lowerLeft(S_0.L) = F3,
transformedEdge(E,p,S_{p+1}) = retainedPassiveTransformedEdge_p for every p.
```

## Method

The proof reuses the existing bedrock lemmas:

- `suffixState_B_retainedPassiveFixedBaseEdgeMatrix` for `-S_0.B = F2_0`;
- `suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_zero_eq_target_of_A1_zero_eq`
  for the active `Ctop` endpoint;
- `retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq` plus
  `suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum`
  for the active `F3` endpoint;
- `retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq` for constructor-side
  transformed-edge reconstruction.

The determinant-unit input for the final `Ctop_last` used in the `A3_last`
solve is derived from the full `A1` determinant-unit family, which itself comes
from the passive unit hypotheses and the solved `A1_0`.

## Role

This is the first fixed-base endpoint package for the retained-passive source
map.  It bundles the three active readbacks and the per-edge transformed-block
reconstruction, but it is not yet a two-sided local coordinate inverse.

## Nonclaims

No bundled retained-passive coordinate-domain structure is defined.  No
source-rank coverage, source/image equality, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT extraction is
proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26 before review.
