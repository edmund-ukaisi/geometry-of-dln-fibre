# Statement card - A2 Case 2 passive theta sector-image support

Date: 2026-06-30.

## Statement

For a theta-domain sector `Omega`, define the passive-sector image

```text
case2PassiveThetaEndpointSectorSet Omega =
  case2PassiveThetaEndpointTopologyTuple '' Omega.
```

Then every restricted theta-domain pushforward

```text
Measure.map case2PassiveThetaEndpointTopologyTuple
  (thetaMeasure.restrict Omega)
```

is supported on that image sector, assuming `Omega`, the image sector, and the
map measurability hypotheses needed by `Measure.map`/`ae_map_iff`.

## Lean Target

Definitions:

```text
case2PassiveThetaSectorSet
case2PassiveThetaEndpointSectorSet
```

Theorem:

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
```

## Proof Idea

`thetaMeasure.restrict Omega` is concentrated on `Omega`.  Applying the
endpoint topology-tuple map sends almost every point into the image
`Y '' Omega`.  Restricting the pushforward measure to that image therefore
does nothing.

## Nonclaims

No exact sector Haar pushforward, determinant-chart Haar transport,
source-prior comparison, finite-scalar domination, bounded-density theorem,
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction is claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-sector-image-support.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-sector-image-support.md
```
