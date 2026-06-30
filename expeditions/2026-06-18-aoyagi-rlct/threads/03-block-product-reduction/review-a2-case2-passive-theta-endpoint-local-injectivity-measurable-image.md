# Review - A2 Case 2 Passive Theta Endpoint Local Injectivity and Measurable Image

Date: 2026-06-30.

## Result

PASS.

## Reviewers

- `Hooke`, xhigh source/scope/math review.
- `Pasteur`, xhigh Lean/API review.

## Source and Scope Review

Hooke checked that the pointwise raw-order bridge is scoped as a concrete
`Case2PassiveTheta` specialization of the pointwise selected-entry bridge, not
as a measure/Haar/RLCT theorem.  The source-chart injectivity theorem uses the
local readback left inverse on `Vread`, and the endpoint topology-tuple
injectivity theorem uses equality of endpoint tuples only to get raw-map
equality, then source-chart equality via `rawChart`, then source-chart
injectivity.

The measurable-image theorem keeps the necessary Lusin-Souslin hypotheses
explicit: Polish/Borel domain and opens-measurable/T2 target.  Since
`case2PassiveThetaEndpointSectorSet` is definitionally the image of the
endpoint topology-tuple map, the measurable-image claim adds no extra image
equality claim.

The slice remains in `DLNFibre.DLN.Aoyagi`, and its statements do not claim
Haar transport, source-prior comparison, source-rank coverage, normal
crossings, pole order, or RLCT extraction.

## Lean/API Review

Pasteur checked the current Lean API.  The large definitional `simpa` in the
concrete raw-order specialization is fragile but matches the existing
specialization style in the file.  The injectivity proof is logically sound,
and the Lusin-Souslin application uses a measurable open set, continuity on the
set, and local injectivity on the same set.

Non-blocking note: the explicit `OpensMeasurableSpace` hypothesis on the
theta-domain in the measurable-image theorem is redundant once `BorelSpace` is
available, but keeping it is harmless and makes the measurable-set derivation
direct.

## Verification

Before the review note was written, the controller checked:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

The full build completed successfully.  It replayed existing modules with
pre-existing warnings outside this slice.

