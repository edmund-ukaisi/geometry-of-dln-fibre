# Statement card - A4 selected-entry analytic atlas producer interface

Status: Lean interface checked locally; xhigh reviews passed.

Reproduction:
`reproduction-selected-entry-analytic-atlas-producer-interface-a4.md`.
Review:
`review-selected-entry-analytic-atlas-producer-interface-a4.md`.

## Target

Introduce a non-redundant supplied producer structure above the finite
selected-entry certificate layer, then project it into the existing supplied
`SelectedEntryAnalyticAtlasBoundary` socket.

## Lean Declarations

File:
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean`.

New data records:

```text
SelectedEntryAnalyticAtlasContext
SelectedEntryAnalyticSourceCoverageData
SelectedEntryAnalyticChartRegularData
SelectedEntryAnalyticTransitionRegularData
SelectedEntryAnalyticUnitRegularData
SelectedEntryAnalyticJacobianVolumeData
SelectedEntryAtlasProducedBranchData
SelectedEntryBranchTerminationData
SelectedEntrySuppliedAnalyticAtlasProducer
```

Projection:

```text
SelectedEntrySuppliedAnalyticAtlasProducer.toBoundary
```

Simp projections:

```text
SelectedEntrySuppliedAnalyticAtlasProducer.toBoundary_chartCertificate
SelectedEntrySuppliedAnalyticAtlasProducer.toBoundary_exponentData
```

## Nontriviality

The producer fields mention one shared atlas context, open domains,
continuity-style regularity, nonzero chart-domain weighted pushforward
equality, separate branch payloads with produced chart/source-domain witnesses,
and well-founded termination data.  There is no constructor from finite
selected-entry chart coverage, finite affine transition regularity, or
`SourceProductionObligation`.

The projection to `SelectedEntryAnalyticAtlasBoundary` is forgetful.  The
coherent object is `SelectedEntrySuppliedAnalyticAtlasProducer`; arbitrary
boundaries built from the exported predicate wrappers do not themselves enforce
one shared context.

## Build

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer
```

passed on 2026-06-28.

## Nonclaims

This interface does not construct the analytic atlas, prove coverage,
regularity, transition regularity, source production, analytic
Jacobian/volume-form compatibility, branch termination, extraction, normal
crossings, pole order, or RLCT.  The density in the Jacobian/volume data is
supplied, not derived from `C.jacobianPrior`.

## Kill Conditions

- Do not add `exists_trivial`.
- Do not add a constructor from finite selected-entry coverage.
- Do not add a constructor from finite affine transition regularity.
- Do not add a constructor from `SourceProductionObligation`.
- Do not merge the actual-width stopped and row-exhausted stopped payloads.
- Do not consume arbitrary forgetful boundaries when shared-context coherence
  is needed; consume the producer.
