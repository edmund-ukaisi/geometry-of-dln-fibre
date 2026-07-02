# Reproduction - A2 Case 2 enlarged following-factor contract constructor

Date: 2026-07-02.

Status: conditional contract constructor for the enlarged following-factor
source image; density identity and density bound remain supplied hypotheses.

## Pen-and-Paper Check

The generic `A2Case2FormalProductSourceImagePieceContract` already records the
data needed by downstream formal-product/source-image consumers:

- a local source chart and readback;
- a theta reference measure and local open domain `V`;
- a measurable chart piece in the source image;
- continuity, injectivity, and readback-left-inverse on `V`;
- a supplied equality of the restricted formal-product measure with a
  bounded-density perturbation of the chart-produced source reference.

The enlarged following-factor local image theorem supplies the chart facts:
after shrinking inside a prescribed open neighborhood `G`, it gives an open
`V`, determinant-chart membership, readback-left-inverse, source-chart
injectivity, source-chart continuity, and measurability of `sourceChart '' V`.

Thus the only remaining inputs for a contract on a specific chart piece are:

```text
chartPiece measurable
chartPiece subset sourceChart '' V
formalProductMeasure|chartPiece =
  (Measure.map sourceChart (thetaReference|V)).withDensity density | chartPiece
density <= bound a.e. on the restricted source reference
```

Those are exactly the still-unproved Jacobian/source-image comparison inputs.
The constructor does not prove them.

## Lean Slice

The new theorem is in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract
```

with name

```text
exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart
```

It returns an existential contract record together with equations identifying
the record fields with the enlarged source chart, readback, `V`, chart piece,
measures, density, and bound.

## Nonclaims

No Jacobian formula, density identity, density bound, formal-product/source
measure comparison, Haar transport, source-rank coverage, normal-crossing
statement, pole order, or RLCT extraction is proved here.
