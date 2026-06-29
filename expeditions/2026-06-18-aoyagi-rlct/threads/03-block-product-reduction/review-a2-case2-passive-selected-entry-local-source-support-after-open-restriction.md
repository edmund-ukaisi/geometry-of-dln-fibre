# Review - A2 Case 2 Passive Selected-Entry Local Source Support After Open Restriction

Date: 2026-06-29.

Status: PASS after reproduction wording repair.

## Reviewed Artifacts

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-case2-passive-selected-entry-local-source-support-after-open-restriction.md
```

## Lean/API Review

Reviewer: Singer the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The theorem derives local a.e. measurability from continuity on `U`: it
  proves `ContinuousOn sourceChart U`, then
  `AEMeasurable sourceChart (sourceMeasure.restrict U)`.
- The support claim is only for `sourceMeasure.restrict U`.
- Base determinant-unit assumptions remain only at `z0`.
- No hidden global determinant-unit, source-prior, Jacobian, coverage, or
  source-rank claim appears.
- File placement in a measure-layer module importing the source slice and
  retained-passive local-measure helper is appropriate.

The reviewer noted stale reproduction wording saying a.e. measurability would
be an explicit hypothesis.  The reproduction note was repaired to state that
measurability is derived from continuity on `U`.

## Source/Scope Review

Reviewer: Descartes the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The theorem is scoped to restricted-measure support: it returns an open `U`
  and concludes support only for
  `Measure.map sourceChart (sourceMeasure.restrict U)`.
- The open determinant domain is inherited from the previous selected-entry
  local source/readback theorem and uses only basepoint determinant-unit
  hypotheses.
- The support proof uses continuity, `ae_restrict_mem`, and the generic support
  helper.  It does not invoke coverage, Haar/source-prior transport, Jacobian
  transport, residual marginal, normal crossings, pole order, or RLCT.

The reviewer independently noted the same stale reproduction wording about
explicit measurability; the note was repaired.

## Controller Resolution

No Lean changes were required after review.  The only issue was documentation
staleness in the reproduction note, now fixed.

Nonclaim boundary remains: no global determinant-chart membership,
selected-entry source-image equality, local coverage, source-rank support or
coverage, determinant-chart Haar pushforward, raw/source Haar transport,
source-prior transport, Jacobian transport, exact localized residual marginal,
normal crossings, pole order, or RLCT.
