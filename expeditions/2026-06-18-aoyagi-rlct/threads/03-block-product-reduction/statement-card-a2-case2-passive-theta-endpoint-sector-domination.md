# Statement card - A2 Case 2 passive theta endpoint-sector domination

Date: 2026-06-30.

## Statement

For the endpoint topology-tuple map `Y` and theta-domain sector `Omega`, let

```text
S_Omega = case2PassiveThetaEndpointSectorSet Omega.
```

If

```text
sourceMeasure.restrict Omega
  <= c * referenceMeasure.restrict Omega,
```

then

```text
(Measure.map Y (sourceMeasure.restrict Omega)).restrict S_Omega
  <= c * (Measure.map Y (referenceMeasure.restrict Omega)).restrict S_Omega.
```

As a bounded-density corollary, if

```text
density <= c
```

almost everywhere for `baseMeasure.restrict Omega`, then the same endpoint
sector domination holds with `sourceMeasure = baseMeasure.withDensity density`
and `referenceMeasure = baseMeasure`.

## Lean Target

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_restrict_endpointSectorSet_le_smul_of_ae_le
```

## Proof Idea

Use `map_le_smul_map_of_le_smul` for the theta-domain domination, then use
the endpoint-sector support theorem to rewrite both restricted pushforwards.
For the density corollary, rewrite `restrict_withDensity` and compare the
density with the constant `c`.

## Nonclaims

No exact passive-sector Haar pushforward, determinant-chart Haar transport,
raw-order Haar transport, source-prior comparison, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction is
claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-endpoint-sector-domination.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-endpoint-sector-domination.md
```
