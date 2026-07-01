# Review - A2 Original Edge-Family Raw-Order Measure Bridge

Date: 2026-07-01.

Reviewer: Sagan the 2nd, xhigh read-only audit.

Status: PASS.

## Scope

Audit the new restricted-pushforward measure bridge for mathematical honesty,
especially the risk of incorrectly treating a restricted chart/source measure
as Haar.

## Findings

The slice is mathematically honest.  The proof compares
`Measure.map L m` with `originalTupleVolume d` as full-space Haar measures,
then restricts the resulting equality to `L '' S`.  It does not assert that
`m.restrict S`, the pushed restricted measure, or the restricted original
tuple volume is Haar.

The composed formal-product theorem is also honest: it uses the existing
retained-passive raw-order change-of-variables theorem, composes with
`rawOrderMatrixTuple`, and then applies the restricted Haar comparison on
`topologyTupleRawOrderSourceRecursiveDetChartSet`.

## Risk Notes

- The scalar orientation is correct:
  `((Measure.map L m).addHaarScalarFactor (originalTupleVolume d)) •
  originalTupleVolume d`.
- Do not later identify this scalar with `1` without a separate normalization
  theorem.
- The target is `originalTupleVolume d`, not `originalEdgeFamilyVolume`.
- The p.13 bridge remains a pointwise chart-domain readout, not a global
  source-coverage theorem.

## API Check

The reviewer independently checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyRawOrderMeasureBridge.lean
```

No edits were made by the reviewer.
