# Review - A2 p.13 left-step conditional raw pushforward consumer

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Ampere the 2nd`.

Verdict: pass, no findings.

## Scope Checked

The review checked the current uncommitted Lean slice in:

```text
lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean
lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean
```

The audited Lean names were:

```text
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
p13ProductCoordinateLeftStepRawTopologyTuple
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
```

## Findings

No correctness or scope findings.

The raw pushforward remains an explicit hypothesis in all consumer layers:

- generic `hpre_map`;
- p.13 explicit raw-preimage `hpre_map`;
- actual constructed left-step `hraw_map`.

The measure orientation and density side were checked.  The proof first pushes
`eta` forward by the raw source tuple, rewrites by the supplied raw-chart Haar
restriction, then applies the existing raw-order pushforward theorem.  The
inverse-Jacobian density remains on
`(m.restrict rawDetChart).withDensity ...` on the target side, not on the
source/product-coordinate domain.

The p.13 specialization uses the almost-everywhere `Ctop.det` unit condition
only to identify the raw-order image of the explicit raw-preimage tuple with
the p.13 raw-order target tuple.  The actual-left-step theorem only transports
the explicit raw-preimage statement through the previously proved equality
`p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple`.

## Nonclaims Reconfirmed

The slice does not prove source coverage, original DLN source/prior transport,
the supplied raw pushforward, signed-box density identification,
product-measure pushforward, regular-suspension certification, normal
crossings, pole order, or RLCT.

## Residual Risk

The reviewer did not run Lean because the review was read-only and builds write
artifacts.  Residual risk is limited to the already-landed raw-order
pushforward/Jacobian theorem beneath this consumer.

## Addendum

A follow-up xhigh scout review in
`review-a2-p13-left-step-ctop-from-raw-chart-support.md` checked the later
hypothesis reduction.  The `Ctop.det` unit fact is now derived from raw-chart
support under the supplied raw pushforward and raw-map a.e. measurability,
rather than taken as a separate consumer input.
