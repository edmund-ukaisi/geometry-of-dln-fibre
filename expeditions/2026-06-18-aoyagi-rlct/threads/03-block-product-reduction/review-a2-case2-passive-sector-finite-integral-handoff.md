# Review - A2 Case 2 passive-sector finite-integral handoff

Date: 2026-06-29.

## Verdict

PASS after documentation scope repair.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

Artifacts:

```text
reproduction-a2-case2-passive-sector-finite-integral-handoff.md
statement-card-a2-case2-passive-sector-finite-integral-handoff.md
```

## Source/Scope Review

Reviewer: Fermat the 4th, xhigh.

Initial verdict: FAIL for documentation wording only.  The first reproduction
draft said "local source-rank coverage near base"; this overclaimed the
underlying neighborhood lemma, which supplies only the inclusion

```text
Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource.
```

Repair: the reproduction now says "retained-passive local-source inclusion
near base" and explicitly states that this is not source-rank coverage and not
an image theorem.

Final verdict: PASS.  The repaired documentation preserves the nonclaims:
no determinant-chart Haar/source-prior transport, source-image equality,
source-rank coverage, exact localized residual marginal equality, normal
crossings, pole order, or RLCT.

## Lean/API Review

Reviewer: Curie the 4th, xhigh.

Verdict: PASS.  No blocking findings.

Checked points:

- The theorem uses the intended chart-produced sector measure
  `sourceMeasure = passiveMeasure.prod weightedBox`, then
  `μ = Measure.map sourceChart (sourceMeasure.restrict V)`.
- The passive/selected-entry coordinate-domain neighborhood `V` and the
  edge-family source-space neighborhood `U` are distinct and not confused.
- The local loss and density assumptions are over `nhdsWithin base localSource`.
- The conclusion integrates over `(μ.restrict (U ∩ sourceStratum)).prod ν`.
- The exponent hypothesis is correctly strengthened to `0 < t`; the proof
  passes `le_of_lt ht` to the residual-source handoff and `ht` to the
  retained-passive local finite-integral consumer.
- Finite passive mass is explicit; the proof derives `IsFiniteMeasure
  passiveMeasure` and infers `SFinite μ` locally.
- The proof uses exactly the intended producer and consumer:
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass`
  and
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource`.

Curie independently checked:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

The direct Lean check passed.

## Controller Verification

Controller local checks:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
scripts/sorries
git diff --check
```

The focused build, direct Lean check, zero-sorry scan, and whitespace check
passed.  The direct axiom probe for the new theorem reported only
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No determinant-chart Haar transport, source-prior transport, passive/source
Jacobian transport, source-image equality, source-rank coverage, exact
localized residual marginal equality, normal crossings, pole order, or RLCT is
proved.
