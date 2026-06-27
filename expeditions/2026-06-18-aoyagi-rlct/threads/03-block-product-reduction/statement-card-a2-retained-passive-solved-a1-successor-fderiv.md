# Statement Card - A2 Retained-Passive Solved A1 Successor Frechet Derivative

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

## Lean Names

```text
fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply
```

## Reproduction

```text
reproduction-a2-retained-passive-solved-a1-successor-fderiv.md
```

## Claim

For a retained-passive `TopologyTuple` and `p : Fin M`,

```text
(fderiv R
  (fun y =>
    (ofTopologyTuple y).toCoordinateData.solvedA1 p.succ) z) v
  = v.1 p.
```

The theorem is stated over real retained-passive `TopologyTuple` coordinates,
not the downstream `RetainedPassiveRawTopologyTuple` abbreviation.

## Method

Since `p.succ != 0`, the solved top-left family unfolds to the stored seed:

```text
solvedA1(p.succ) = A1seed(p.succ).
```

The retained-passive seed at a successor index is the passive raw coordinate
`A1passive p`, so the map is judgmentally the coordinate projection
`y |-> y.1 p` after unfolding.  The Frechet derivative of this continuous
linear projection is itself.

## Role

This moves the successor solved-`A1` derivative formula into the upstream
derivative layer.  It is intended as the easy half of the solved-`A1`
derivative split needed before source-staging the remaining `d(solvedA1 p)`
terms in the retained-passive `dEarly` recurrence.

## Nonclaims

No determinant-chart hypothesis is used or needed.  The zero branch
`solvedA1(0)` remains separate and still requires the inverse-tail product
rule.  This statement is not a recursive `dTail` formula, not a complete
`dPcast` source-staging theorem, and not a determinant, measure,
normal-crossing, pole-order, or RLCT theorem.
