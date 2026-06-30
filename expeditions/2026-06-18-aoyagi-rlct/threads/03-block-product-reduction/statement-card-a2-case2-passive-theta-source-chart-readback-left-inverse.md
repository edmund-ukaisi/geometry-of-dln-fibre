# Statement Card - A2 Case 2 Passive Theta Source-Chart Readback Left Inverse

Date: 2026-06-30.

## Lean Claim

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

New public names:

```text
endpointTransport_symm_endpointTransport
case2PassiveThetaEndpointSourceChartReadback
case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
```

## Mathematical Content

`endpointTransport_symm_endpointTransport` proves that endpoint-transporting a
retained-passive nonredundant coordinate datum along endpoint equivalences and
then transporting back along their inverses recovers the original datum.

`case2PassiveThetaEndpointSourceChartReadback` reads a full `Case2PassiveTheta`
coordinate from an endpoint p.13 source edge family: passive fields come from
`sourceReadback`, transported back through the endpoint equivalences; the
selected residual field comes from
`case2PassiveThetaEndpointInverseReadout`.

`case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData`
is the pointwise algebraic bridge: if the source-family readback equals the
endpoint retained data of `theta` and the selected-entry inverse readout equals
`theta.yNext`, then the source-chart readback equals `theta`.

`exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse` says
that near a determinant-sector, nonzero-pivot base theta point there is an open
neighborhood `V` such that

```text
readback (sourceChart z) = z
```

for every `z ∈ V`.

## Proof Source

Pen-and-paper reproduction:

```text
reproduction-a2-case2-passive-theta-source-chart-readback-left-inverse.md
```

The proof uses the existing determinant-domain source-readback theorem,
intersects that open set with the open selected-pivot nonzero condition, and
then applies the selected-entry inverse-readout equality.

## Nonclaims

This slice does not prove endpoint-sector image measurability, source-image
equality, exact passive-sector Haar transport, determinant-chart Haar
transport, raw-order Haar transport, source-prior comparison, source-rank
coverage, normal crossings, pole order, or RLCT extraction.

