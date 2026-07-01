# Review - A2 Case 2 determinant-sector determinant-chart support

Date: 2026-07-01.

Status: controller review PASS; xhigh reviewer `Locke the 3rd` PASS.

## Checks

- The theorem assumes `Omega subset case2PassiveThetaDetSector`; it does not
  construct the determinant sector or choose a passive reference box.
- The target set is exactly `topologyTupleDetChartSet`, the retained-passive
  topology-tuple determinant chart used by the downstream raw-image sockets.
- The proof is support-only: pointwise determinant-sector membership gives
  a.e. determinant-chart membership, and `ae_map_iff` transports it through
  `Measure.map Y`.
- The theorem is measure-generic in `thetaMeasure`; this is safe because only
  support is claimed.
- The a.e.-measurability of `Y` is explicit.  Downstream concrete wrappers can
  discharge it from `continuous_case2PassiveThetaEndpointTopologyTuple`.

## Boundary

This is not the passive-reference Haar/Lebesgue change-of-variables theorem.
It does not prove `Measure.map Y (passiveReferenceSource.restrict V) <= c •
rawHaar.restrict rawDetChart`; it only proves that the left-hand measure is
supported on `rawDetChart` when `V` lies in the determinant sector.
