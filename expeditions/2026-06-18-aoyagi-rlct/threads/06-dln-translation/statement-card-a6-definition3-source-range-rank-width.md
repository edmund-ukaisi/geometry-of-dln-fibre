# Statement card - A6 Definition 3 source-range rank-width

Status: Lean bridge landed.

Reproduction:
`reproduction-definition3-source-range-rank-width-a6.md`.

Independent review:
`review-definition3-source-range-rank-width-a6.md`.

## Target

Remove one repeated supplied hypothesis from the Definition 3/final-socket
path:

```text
forall s, 1 <= s -> s <= N+1 -> r <= H s.
```

The bridge derives it from the A2 source-rank boundary plus an explicit
identification of Aoyagi's layer-width function with the layer finranks.

## Lean Slice

Lean now adds

```text
DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
```

with:

```text
paperTotalMap_rank_le_layer_finrank
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_sourceRankStratum
```

The first theorem proves `r <= finrank K (W k)` for every paper layer `W k`
from the product-rank equality

```text
Module.finrank K (LinearMap.range (paperTotalMap W B)) = r.
```

The second theorem rewrites this through the explicit convention

```text
H (k.val + 1) = Module.finrank K (W k).
```

The third theorem feeds the resulting source-range rank-width hypothesis into
the existing Definition 3 source-data ceiling constructor.

## Nonclaims

Selected cutpoints and `AoyagiDefinition3SourceData` remain supplied.

The bridge does not prove exact-rank strata are open, chart coverage,
normal crossings, finite exponent formula equalities, pole order, or RLCT.

## Verification

Focused verification:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
```

passed on 2026-06-24.
