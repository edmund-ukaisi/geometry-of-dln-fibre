# Review - A2 Case 2 passive-sector source-stratum-bounds finite integral

Date: 2026-06-29.

## Verdict

PASS.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

Artifacts:

```text
reproduction-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md
statement-card-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md
```

## Source/Scope Review

Reviewer: Mencius the 4th, xhigh.

Verdict: PASS.  No math/source/scope inaccuracies found.

Checked points:

- The theorem states loss and density bounds on
  `nhdsWithin base sourceStratum`, where `sourceStratum` is the fixed-base
  source-rank stratum, not the retained-passive `localSource`.
- The theorem keeps `0 < t` and the selected-entry critical inequality explicit.
- The proof uses only residual hypotheses on `localSource`, source-stratum
  measurability, and the local inclusion supplied by
  `exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase`.
- The docs' nonclaims match the formal route: no source-rank coverage,
  determinant/Jacobian/source-prior transport, residual marginal equality,
  normal crossings, pole order, or RLCT extraction is claimed.

Mencius independently checked:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

The direct Lean check passed.

## Lean/API Review

Reviewer: Dalton the 4th, xhigh.

Verdict: PASS.  No concrete findings.

Checked points:

- The target theorem elaborates and is a sibling of the earlier local-source-bound
  theorem, not a mutation of that theorem.
- The statement is the intended source-stratum-bound variant: assumptions are on
  `nhdsWithin base sourceStratum`, and the final integral is over
  `mu.restrict (U ∩ sourceStratum)`.
- The proof obtains residual hypotheses from
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass`.
- The proof establishes source-stratum measurability, obtains the self-base
  local coverage inclusion, and feeds
  `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource`.
- Non-vacuity checks passed: the returned coordinate-domain `V` is open and
  contains `z0`, and the final `U` contains `base`.  Zero passive measure remains
  allowed by the finite-mass hypothesis; this is not an API bug.

Dalton independently checked:

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
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

The focused build, direct warning-level Lean check, zero-sorry scan, whitespace
check, and full `DLNFibre` build passed using local Lake.  The full build emitted
only pre-existing replay warnings from other modules.  The direct axiom probe for
the new theorem reported only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No determinant-chart Haar transport, source-prior transport, passive/source
Jacobian transport, source-image equality, source-rank coverage, exact localized
residual marginal equality, normal crossings, pole order, or RLCT is proved.
