# Review - A2 p.13 Source-Set Measure Bridge

Date: 2026-07-01.

Reviewer: Kepler the 2nd, xhigh read-only audit.

Status: PASS.

## Scope

Audit the p.13 source-set measure bridge for mathematical honesty and source
fidelity.

## Findings

The bridge is mathematically honest.  The pointwise theorem is explicitly
chart-domain only through the hypothesis

```text
y ∈ topologyTupleRawOrderSourceRecursiveDetChartSet.
```

Both measure theorems keep the full-space tuple Haar scalar

```text
(Measure.map ... m).addHaarScalarFactor (originalTupleVolume d)
```

and restrict `originalEdgeFamilyVolume` to the named
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet`.

The named source set is the fixed-base retained-passive p.13
source-recursive determinant-chart set, not an original source-rank coverage
claim.  The use of the existing `RetainedPassiveLocalJacobianMeasure`
source-set theorem and support theorem is appropriate for the formal-product
statement.

## Risk Notes

- Do not use the pointwise p.13 source-chart equality outside the raw source
  chart.
- Do not identify the scalar with `1` without a separate normalization
  theorem.
- Do not cite this as original source-rank coverage, restricted Haar
  structure, normal crossings, pole order, or RLCT extraction.

No edits were made by the reviewer.

## Follow-up Chart-piece Corollary Review

Date: 2026-07-01.

Reviewer: Hegel the 2nd, xhigh read-only audit.

Status: PASS.

Scope: audit the two chart-piece restriction corollaries added to
`OriginalEdgeFamilyP13SourceMeasureBridge.lean` and the corresponding
reproduction/statement-card updates.

Findings: no issues.  The corollaries keep the same tuple-side full-space Haar
scalar, require `chartPiece ⊆ sourceSet`, and only restrict the already-proved
source-set equalities.  They do not infer passive-theta source-image
containment or scalar normalization.

Verification noted by reviewer:

```text
lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```
