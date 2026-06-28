# Review - selected-entry analytic atlas producer interface

Date: 2026-06-28.

Status: PASS.

Scope: Lean interface
`DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer` and the matching A4
expedition notes.

## Lean Interface Review

Reviewer: Epicurus the 2nd, xhigh.

Verdict: PASS after hardening.

Findings:

- `SelectedEntrySuppliedAnalyticAtlasProducer` has one `atlasContext` reused by
  coverage, chart regularity, transition regularity, unit regularity,
  Jacobian/volume data, and source production.
- `SelectedEntryAnalyticJacobianVolumeData` now rules out the previous zero
  measure loophole with `source_restrict_neZero`, and its compatibility field
  is a chart-domain weighted pushforward equality.
- `SelectedEntryProducedBranchPayload` is parameterized by the shared context,
  includes produced chart-domain and source-domain membership fields, and
  carries an actual `producedSourceData` witness.
- Continuing, actual-width stopped, and row-exhausted stopped branches remain
  separate payload channels tied back to the same branch state.
- The predicate wrappers and `toBoundary` projection are explicitly forgetful:
  shared-context coherence belongs to the producer, not to arbitrary
  boundaries assembled from the exported predicates.

Remaining limitation: `density` is still supplied analytic data, not derived
from `C.jacobianPrior`.  This is intended for this interface slice and should
not be described as a proved Jacobian formula.

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb \
  DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer
```

## Source-Boundary Review

Reviewer: Tesla the 2nd, xhigh.

Verdict: PASS.

Findings:

- The notes preserve the A4 source boundary: Aoyagi pp. 19-22 are treated as
  finite Case 2 algebra only, not analytic atlas or source-production data.
- The forbidden constructors remain excluded: no constructor from finite
  selected-entry coverage, finite affine transition regularity, or
  `SourceProductionObligation`.
- Shared atlas context, nonzero chart-domain weighted pushforward equality,
  and branch separation are accurately recorded.
- No extraction, RLCT, or final Theorem 2 overclaim was found.

