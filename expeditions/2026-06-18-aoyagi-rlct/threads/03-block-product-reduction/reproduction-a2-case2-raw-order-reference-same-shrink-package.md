# Reproduction - A2 Case 2 raw-order reference same-shrink package

Date: 2026-07-01.

Status: pen-and-paper reproduction and Lean proof complete.

## Question

The current Lean interface has separate existential theorems for support,
domination, endpoint/raw/source-chart handoff, and density transport.  Since
each theorem may choose its own open set `V`, downstream consumers cannot
combine those facts without another shrink argument.  Can the existing local
Aoyagi p.13 raw-order/source-chart package supply all of them on one `V`?

## Setup

Fix a Case 2 passive-theta base point `z0` in the determinant sector with
nonzero pivot, and an open neighborhood `G`.  The existing local theorem gives
one open set

```text
V subset G
```

together with determinant-chart membership for

```text
Y(theta) =
  case2PassiveThetaEndpointTopologyTuple ... theta
```

and the two-stage map package for

```text
rawMap(theta) = topologyTupleEdgeRawOrder (Y(theta))

sourceChart(theta) =
  case2PassiveThetaEndpointSourceChart ... theta.
```

The named raw-order reference image is

```text
rawOrderReferenceImage =
  Measure.map rawMap (referenceSource.restrict V).
```

## Same-Shrink Consequences

On this same `V`:

- determinant-chart membership and continuity of raw order on the determinant
  chart give a.e. measurability of `rawMap`;
- the image measure is supported on
  `topologyTupleRawOrderSourceRecursiveDetChartSet`;
- passive-field domination by the coordinate passive-field reference pushes
  forward to domination by `rawOrderReferenceImage`;
- the endpoint reference image pushed by `topologyTupleEdgeRawOrder` is exactly
  `rawOrderReferenceImage`;
- the p.13 raw-order chart pushes `rawOrderReferenceImage` to the direct
  source-chart image of `referenceSource.restrict V`;
- every supplied raw density a.e. measurable for `rawOrderReferenceImage`
  transports through the p.13 raw-order chart to the composed-density
  source-chart image.

## Boundary

This package only aligns local image-measure bookkeeping on one shrink.  It
does not identify `rawOrderReferenceImage` with raw Haar, determinant-chart
Haar, original edge-family volume, or an original/source prior.  It also does
not prove source-image coverage, source-rank coverage, normal crossings, pole
order, or RLCT extraction.

## Kill Conditions

- Do not prove the package by chaining the existing separate `exists V`
  theorems.
- Do not replace the named image measure by unrestricted raw Haar.
- Do not assume global measurability of `rawMap`; use local determinant-chart
  membership.
- Do not claim the supplied raw density comes from Aoyagi's original prior.

## Lean Check

Lean witness:

```text
exists_open_subset_case2PassiveThetaRawOrderReferenceImage_same_shrink_package
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
