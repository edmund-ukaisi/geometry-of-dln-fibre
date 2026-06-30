# Statement Card - A2 Case 2 passive theta bounded-density global-Jacobian finite integral

Status: proved in Lean.

Reproduction:

```text
reproduction-a2-case2-passive-theta-bounded-density-global-jacobian-finite-integral.md
```

Review:

```text
review-a2-case2-passive-theta-bounded-density-global-jacobian-finite-integral.md
```

## Claim

For the concrete full `Case2PassiveTheta` coordinate domain, a theta-domain
measure of the form

```text
(passiveSource.withDensity jacobianDensity).withDensity sourceDensity
```

satisfies the retained-passive residual-source hypotheses and the p.13
source-stratum finite-integral handoff after shrinking to a local punctured
sector, provided `sourceDensity` is bounded above a.e. on that local sector
with respect to `passiveSource.withDensity jacobianDensity`.

## Existing Inputs

The slice uses:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
restrict_withDensity
withDensity_mono
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
```

## Payoff

This removes the caller-supplied local domination field

```text
candidateMeasure.restrict W <= c •
  (passiveSource.withDensity jacobianDensity).restrict W
```

for the important prior-shaped case where the candidate measure is obtained by
adding one more bounded density to the global Jacobian-weighted passive
product measure.

## Nonclaims

No determinant-chart Haar transport, raw-order Haar transport, original DLN
source-prior identification, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal-crossing construction, pole-order
theorem, or RLCT extraction is proved by this card.

## Verification

Passed before commit:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
lake env lean -E warning DLNFibre.lean
./scripts/sorries
git diff --check
```

Touched-file marker scans were clean.
