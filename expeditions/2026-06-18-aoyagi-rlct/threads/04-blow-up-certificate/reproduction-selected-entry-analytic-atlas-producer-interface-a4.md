# Reproduction - selected-entry analytic atlas producer interface

Date: 2026-06-28.

Status: interface design and Lean slice.  This is not an Aoyagi calculation
and does not claim analytic atlas construction.

## Question

After the frontier recheck, what is the smallest Lean interface that is not
just another wrapper around finite selected-entry algebra?

The answer is a supplied producer structure above the finite
`AoyagiNormalCrossingChartCertificate`, with data-bearing fields for analytic
coverage, chart regularity, transition regularity, unit regularity,
Jacobian/volume compatibility, branchwise source production, and termination.
It should project into the existing `SelectedEntryAnalyticAtlasBoundary`
socket, but it should not supply any constructor from:

- finite selected-entry chart coverage;
- `SelectedEntryFiniteAffineTransitionRegularFamily`;
- `SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`;
- `SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`.

## Source and Lean Inputs

The source audit says Aoyagi pp. 5-6 provide the general analytic
normal-crossing background and pp. 14-22 provide finite local blow-up algebra.
The analytic extraction theorem remains cited.  The source does not define
DLN-specific atlas domains, overlap maps, measure pushforwards, produced
successor/suffix data, or branch termination as a global atlas theorem.

Existing Lean already has:

- `AoyagiNormalCrossingChartCertificate`, a finite chart/exponent spine;
- `SelectedEntryAnalyticAtlasBoundary`, a supplied socket with arbitrary
  analytic predicate fields;
- finite selected-entry coverage and finite affine transition certificates;
- formula-level `SourceProductionObligation` constructors and consumers;
- final bridges that still require extraction and finite formula hypotheses
  explicitly.

## Interface Reproduction

The new Lean interface in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean` adds
concrete data records:

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

The records intentionally mention data that finite selected-entry algebra does
not contain:

- one shared atlas context with open source and chart domains;
- chart-map and coordinate continuity on chart domains;
- transition maps on overlap domains preserving the represented source point;
- regular unit-factor data on chart domains;
- chart-domain weighted pushforward equality against a nonzero restricted
  source measure;
- separate continuing, actual-width stopped, and row-exhausted stopped branch
  payloads whose produced points lie in the shared chart domains and whose
  produced parameters lie in the shared source domain;
- a well-founded branch-step relation.

The only Lean projection is:

```text
SelectedEntrySuppliedAnalyticAtlasProducer.toBoundary
```

It wraps the supplied data into the predicate fields expected by
`SelectedEntryAnalyticAtlasBoundary`.

The projection is forgetful.  The existing boundary socket stores separate
predicate fields, so an arbitrary boundary assembled from the exported
predicate wrappers need not remember that all fields came from one context.
The coherent object is the producer itself; `toBoundary` is only a bridge to
older downstream sockets.

## Branch Fidelity

The branch payload record keeps three payload types:

```text
continuingPayload
actualWidthStoppedPayload
rowExhaustedStoppedPayload
```

This follows the branch scout's warning.  Continuing source production needs a
real produced successor or full `C'^(S+1)`.  Actual-width stopping needs
terminal rows and suffix data produced from the chart, not merely a supplied
`Cterm`.  Row-exhausted stopping carries transported rows involving the
`Q^-1 C` correction; it is not original old-row data unless an actual-width
hypothesis is separately proved.  The interface does not know the future
concrete source-data type, so each branch payload supplies that type together
with an actual `producedSourceData` witness, a produced chart point in the
shared chart domain, and the corresponding produced parameter in the shared
source domain.

## Nonclaims

The new Lean file does not:

- construct chart domains;
- prove source-neighborhood coverage;
- prove analytic chart or transition regularity;
- prove analytic Jacobian/volume-form compatibility;
- derive the supplied density from `C.jacobianPrior`;
- source-produce `Csucc`, `Cterm`, `C'^(S+1)`, or suffix data;
- prove branch termination;
- produce an extraction hypothesis;
- prove normal crossings, pole order, or RLCT.

## Kill Conditions

- If a future theorem can fill the producer from finite selected-entry
  coverage plus finite affine transition regularity, the producer is too weak.
- If the branch payloads collapse actual-width stopped and row-exhausted
  stopped data, the producer is wrong.
- If measure/Jacobian compatibility is replaced by a formal pivot-first
  determinant identity, the producer overclaims.
- If the restricted source-measure target can be zero, the producer is too
  weak for analytic volume compatibility.
- If `toBoundary` is described as analytic extraction or final Theorem 2, the
  statement overclaims.
- If a downstream theorem needs shared-context coherence after projection, it
  should consume `SelectedEntrySuppliedAnalyticAtlasProducer`, not an arbitrary
  `SelectedEntryAnalyticAtlasBoundary` using the forgetful predicates.
