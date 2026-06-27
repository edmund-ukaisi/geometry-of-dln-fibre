# Statement Card - A2 Retained-Passive Actual Derivative Passive A3 Identity

Status: reproduced, Lean-proved, and reviewed.

## Claim

For a retained-passive tuple `z` in the determinant chart, tangent vector `v`,
and passive nonterminal index `p : Fin M`, the actual Frechet derivative of
the raw-order map leaves the stored lower-left passive coordinate unchanged:

```text
((D raw z) v).A3passive p = v.A3passive p.
```

Here `raw = topologyTupleEdgeRawOrder` and `D raw z` is the ambient Frechet
derivative `fderiv R raw z`.

The matching raw-edge readout agrees with the point-specialized formal
raw-order map:

```text
rawEdgeTupleA3 ((D raw z) v) p.castSucc
  = (retainedPassiveFormalRawOrderJacobianAt z v).A3passive p.
```

## Lean Status

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
```

New theorem names:

```text
fderiv_topologyTupleEdgeRawOrder_A3passive_apply
rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt
```

## Reproduction

```text
reproduction-a2-retained-passive-actual-derivative-a3passive-identity.md
```

Review:

```text
review-a2-retained-passive-actual-derivative-a3passive-identity.md
```

## Dependencies

- raw lower-left readout `rawEdgeTupleA3_castSucc`;
- passive raw-order block formula `topologyTupleEdgeRawOrder_A3passive`;
- nonterminal solve rule `retainedPassiveSolvedA3_eq_of_ne_last`;
- endpoint guard `Fin.castSucc_ne_last p`;
- differentiability of `topologyTupleEdgeRawOrder` on `topologyTupleDetChartSet`;
- formal raw-order apply formula `retainedPassiveFormalRawOrderJacobian_apply`.

## Nonclaims

This does not cover the terminal lower-left `F3` coordinate.  It does not
prove full equality between the actual Frechet derivative and the formal
raw-order map, a signed or absolute determinant formula, a measure pushforward,
source-prior transport, source-rank coverage, normal crossings, pole order, or
RLCT.
