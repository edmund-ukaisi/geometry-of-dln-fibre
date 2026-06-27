# Statement card - A2 retained-passive raw-order determinant formula

Status: reproduced on paper from the local Lean chart definitions, with the
`LastTop` endpoint convention independently checked; not yet implemented as an
explicit Lean determinant formula.

## Claim

On the retained-passive determinant chart, the absolute determinant of the
ambient derivative of `topologyTupleEdgeRawOrder` factors as

```text
|det Tail|^(-|rho|)
* |det LastTop|^(|kappa'_(M+1)|)
* product_{p : Fin (M+1)} |det (A p)|^(|kappa'_p|),
```

where `A p` is the solved top-left family,
`Tail = A_M * ... * A_1` with empty product `1`, and `LastTop` is the one-edge
residual-factor product used in the solved final lower-left block.

Endpoint convention: `LastTop = A_M` for `M > 0`, while `LastTop = Ctop` for
`M = 0`.  It is not the same object as `Tail`.

## Current Lean status

Already proved:

- `topologyTupleEdgeRawOrderFDerivAbsDet` names the abstract absolute
  determinant.
- The determinant is a unit, positive, and continuous on
  `topologyTupleDetChartSet`.
- `linearMap_det_mulLeftLinearMap` and `linearMap_det_mulRightLinearMap` prove
  the rectangular determinant API for matrix left/right multiplication.

Not yet proved:

- the displayed product formula;
- the derivative-level factorization into determinant-one shears and the three
  nontrivial factor families.

## Reproduction artifact

`reproduction-a2-retained-passive-raw-order-determinant-formula.md`

## Dependencies

- `TopologyTuple` product order and `ofTopologyTuple` readback.
- `retainedPassiveSolvedA1` and `retainedPassiveA1TailAfterFirst`.
- `retainedPassiveSolvedA3`.
- raw block formulas for `topologyTupleEdgeRawOrder`.
- `residualFactorProduct` one-edge/self endpoint conventions.
- `linearMap_det_mulLeftLinearMap` and `linearMap_det_mulRightLinearMap` for
  matrix left/right multiplication.

## Caveats

The PDF could not be freshly extracted in the current VM.  Before this claim is
treated as source-faithful Aoyagi p.13 content, a manual/PDF-readable check
must compare the local retained-passive chart against Aoyagi's printed
coordinate substitutions.

This is not a source-prior pushforward theorem, not selected-entry chart
coverage, not source-rank coverage, not normal crossings, and not RLCT.
