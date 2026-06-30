# Statement card - A2 Case 2 passive theta source-measure adapter

Date: 2026-06-30.

## Statement

Specialize the generic passive selected-entry source-measure support theorem to
the concrete full passive-sector coordinate type `Case2PassiveTheta`.

For a base theta point in the determinant sector with nonzero selected pivot,
and for any source-domain measure on theta coordinates, there is an open
punctured determinant-sector neighborhood `V` such that the chart-produced
source measure

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

is supported on the retained-passive p.13 local source and its selected
residual inverse readout is exactly the `yNext` marginal of the restricted
theta-domain measure.

## Lean Target

Module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Theorem:

```text
exists_open_measure_map_case2PassiveThetaEndpointSourceChart_puncturedSector_inverseReadout_eq_yNext
```

Auxiliary public names:

```text
case2PassiveThetaEndpointSourceChart
case2PassiveThetaEndpointResidualCoordEquiv
case2PassiveThetaEndpointInverseReadout
```

The proof should instantiate the existing generic theorem

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
```

with `eta = Case2PassiveTheta.PassiveFields`.

Measure-side hypotheses include `MeasurableSpace` and
`OpensMeasurableSpace` instances on the passive-fields product domain.  The
adapter does not construct these instances; it consumes them in the same way
the generic theorem consumes such structure on an arbitrary passive parameter
type.

## Nonclaims

No determinant-chart Haar transport, raw-order Haar transport, source-prior
transport, exact passive-sector pushforward, dominated passive-sector
comparison, finite-integral transfer, source-image equality, source-rank
coverage, normal crossings, pole order, or RLCT extraction is claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-source-measure-adapter.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-source-measure-adapter.md
```
