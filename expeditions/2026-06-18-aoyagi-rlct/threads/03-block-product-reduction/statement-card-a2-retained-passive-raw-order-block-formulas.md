# Statement Card - A2 retained-passive raw-order block formulas

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
topLeftCorner_retainedPassiveFixedBaseEdgeMatrix
upperRightBlock_retainedPassiveFixedBaseEdgeMatrix
lowerLeftBlock_retainedPassiveFixedBaseEdgeMatrix
lowerRightBlock_retainedPassiveFixedBaseEdgeMatrix
toBlocks11_retainedPassiveFixedBaseEdgeMatrix
toBlocks12_retainedPassiveFixedBaseEdgeMatrix
toBlocks21_retainedPassiveFixedBaseEdgeMatrix
toBlocks22_retainedPassiveFixedBaseEdgeMatrix
topologyTupleEdgeRawOrder_A1passive
topologyTupleEdgeRawOrder_F2
topologyTupleEdgeRawOrder_A3passive
topologyTupleEdgeRawOrder_C
topologyTupleEdgeRawOrder_Ctop
topologyTupleEdgeRawOrder_F3
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-derivative-jacobian-plan.md
```

## Claim

The raw blocks of the fixed-base retained-passive edge matrix are exactly

```text
X_p = A_p + F2full_(p.succ) * L_p
B_p = -(A_p * F2full_(p.castSucc))
        + F2full_(p.succ) * (C_p - L_p * F2full_(p.castSucc))
Y_p = L_p
Z_p = C_p - L_p * F2full_(p.castSucc).
```

Consequently, the retained-passive raw-order endomap has component formulas
obtained by packing `X`, `B`, `Y`, and `Z` into the existing `TopologyTuple`
order.

## Method

The proof is a direct multiplication of

```text
fromBlocks 1 F2full_(p.succ) 0 1
```

with the retained-passive transformed edge

```text
fromBlocks A_p (-(A_p * F2full_(p.castSucc))) L_p
  (C_p - L_p * F2full_(p.castSucc)).
```

The tuple formulas then unfold `topologyTupleEdgeRawOrder`,
`edgeFamilyRawOrderTuple`, `topologyTupleEdgeMatrix`, and the nonredundant
edge-map projection.

## Role

This is the first derivative-facing component formula layer for the
retained-passive raw-order endomap.  It gives the explicit polynomial/rational
component map that the next `DifferentiableAt` and formal Jacobian theorem
will use.

## Nonclaims

No derivative, determinant formula, density, measure pushforward, image
equality, source-rank coverage, normal crossings, pole order, or RLCT
statement is proved here.
