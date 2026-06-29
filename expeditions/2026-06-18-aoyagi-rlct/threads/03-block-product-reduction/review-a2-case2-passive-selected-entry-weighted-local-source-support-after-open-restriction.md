# Review - A2 Case 2 Passive Selected-Entry Weighted Local Source Support After Open Restriction

Date: 2026-06-29.

Status: PASS.

## Reviewed Artifacts

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-case2-passive-selected-entry-weighted-local-source-support-after-open-restriction.md
```

## Lean/API Review

Reviewer: Nietzsche the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The theorem derives base a.e. measurability from continuity on `U`, exactly
  as in the unweighted theorem.
- It transfers a.e. measurability to
  `(sourceMeasure.restrict U).withDensity density` using
  `AEMeasurable.mono_ac` and `withDensity_absolutelyContinuous`.
- It transfers a.e. local-source membership from `sourceMeasure.restrict U` to
  the weighted measure using `(withDensity_absolutelyContinuous _ _).ae_le`.
- The final step applies
  `measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem` with
  `eta := weighted`, matching the helper API.
- The conclusion is only support of
  `Measure.map sourceChart ((sourceMeasure.restrict U).withDensity density)`
  on the retained-passive local source.

No Lean/API findings were reported.

## Source/Scope Review

Reviewer: Schrodinger the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The density is arbitrary; the theorem does not identify it with a Jacobian.
- The measure in the conclusion is exactly the weighted restriction to the
  constructed open determinant domain `U`.
- The conclusion is only `mu.restrict localSource = mu`, not topological
  support, coverage, or a transport formula.
- The proof reuses the prior open determinant-domain source/readback theorem
  and then uses only `withDensity_absolutelyContinuous` plus the generic
  local-source support helper.
- The reproduction note and statement card keep the nonclaim boundary explicit.

No source/scope findings were reported.

## Controller Resolution

No Lean or documentation repairs were required after review.

Nonclaim boundary remains: no Jacobian identification, global determinant-
chart membership, selected-entry source-image equality, local coverage,
source-rank support or coverage, determinant-chart Haar pushforward,
raw/source Haar transport, source-prior transport, Jacobian transport, exact
localized residual marginal, normal crossings, pole order, or RLCT.
