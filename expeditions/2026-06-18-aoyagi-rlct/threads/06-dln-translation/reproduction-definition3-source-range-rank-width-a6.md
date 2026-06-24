# Reproduction - Definition 3 source-range rank-width

Date: 2026-06-24.

Status: pen-and-paper reproduction and Lean target record.

## Question

Several Definition 3 and final-socket theorems currently require the supplied
source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

Aoyagi's DLN setup has layer widths `H^(s)` and product rank `r`.  Since the
total product factors through every layer, the product rank is bounded by every
layer dimension.  The next source-moving target is to formalize this elementary
rank-width provenance from the existing A2 product-rank data.

## Source Anchors

Aoyagi PDF p. 8 sets up the DLN dimensions and defines

```text
M^(s) = H^(s) - r,  s = 1,...,L+1.
```

Aoyagi PDF pp. 11-13 records the rank-stratum/product-rank setup: the total
product has rank `r`, and the intermediate layer maps have ranks at least `r`.
PDF p. 13 then reuses `M^(s)=H^(s)-r` in the reduced-width recurrence.

This step uses only the elementary rank bound forced by factorization through
layer vector spaces.  It does not use the normal-crossing extraction citation.

## Existing Lean Inputs

The A2 source-rank boundary is

```text
paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

from `ProductReductionBoundary.lean`.  Membership gives:

```text
Module.finrank K (LinearMap.range (paperTotalMap W B)) = r,
x in paperEndpointFixedBaseEdgeRankStratum W Cedge rEdge,
forall p, r <= rEdge p.
```

The rank-width proof uses only the total product rank equality.  The edge-rank
stratum and inequalities are carried by the source-rank boundary but are not
needed for this particular layer-dimension bound.

The current A6/Definition 3 handoffs consume:

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s
```

for example in

```text
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth.
```

The Lean indexing convention for this bridge will be:

```text
H (k.val + 1) = Module.finrank K (W k)
```

for `k : Fin (N+1)`, so the source range is `s=1,...,N+1`.
The direct Definition 3 consumer therefore specializes the existing `L`
parameter to `N`, i.e. it consumes

```text
S : AoyagiDefinition3SourceData N ell H r C.
```

## Pen-and-paper Argument

Let the paper-order layer vector spaces be `W_0,...,W_N`.  The total product
map is

```text
P : W_N -> W_0.
```

Suppose

```text
rank(P) = r.
```

For any layer `W_k`, the total product factors through that layer:

```text
W_N -> W_k -> W_0.
```

Choose a complement `U_0` to `ker(P)` in the source `W_N`.  Then the restriction
of `P` to `U_0` is injective and maps onto `range(P)`, so

```text
dim U_0 = rank(P) = r.
```

Lean implements this through the reversed source-to-target chain.  Since

```text
reverseVertex W j = W (j.rev),
```

the through-subspace at paper layer `W_k` is indexed by `k.rev`, not by `k`.
Call it `U_{k.rev}`.  Because `U_0` is disjoint from the kernel of the full
product, it is also disjoint from the kernel of each prefix map that occurs in
the factorization.  Therefore

```text
dim U_{k.rev} = dim U_0 = r.
```

Since `U_{k.rev}` is a subspace of `reverseVertex W (k.rev) = W_k`,

```text
r = dim U_{k.rev} <= dim W_k.
```

Under the dimension identification `H(k+1)=dim W_k`, this gives

```text
r <= H(k+1).
```

Now if `s` is any natural number with `1 <= s <= N+1`, take `k=s-1`.  Then
`k : Fin (N+1)` and `k+1=s`, so

```text
r <= H s.
```

This proves the required source-range rank-width hypothesis.

## Lean Shape

Add a new downstream module:

```text
DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
```

First theorem:

```text
paperTotalMap_rank_le_layer_finrank
```

from the product-rank equality, prove

```text
forall k : Fin (N+1), r <= Module.finrank K (W k).
```

This should use the already-proved through-subspace theorem
`exists_chain_throughSubspaces` applied to the reversed chain
`reverseVertex W`, `reverseEdge W B`.

Second theorem:

```text
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth
```

from stratum membership plus the dimension identification

```text
forall k : Fin (N+1), H (k.val + 1) = Module.finrank K (W k)
```

prove

```text
forall s, 1 <= s -> s <= N+1 -> r <= H s.
```

Optional direct consumer:

```text
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_sourceRankStratum
```

which calls the existing
`exists_selectedReducedWidthCeilData_of_rankWidth` after producing the
rank-width hypothesis.

Lean follow-through:

```text
DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
```

now contains these three declarations:

```text
paperTotalMap_rank_le_layer_finrank
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_sourceRankStratum
```

The focused build

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
```

passed on 2026-06-24.

## Nonclaims

This bridge does not construct selected cutpoints or prove
`AoyagiDefinition3SourceData`.

It does not prove exact-rank strata are open, chart coverage, source
production, normal crossings, finite exponent formula equalities, pole order,
or RLCT.

The dimension identification `H(k+1)=finrank(W k)` remains explicit; this
avoids silently choosing a paper/display orientation.
