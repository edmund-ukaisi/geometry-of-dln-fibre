# Statement Card - A2 source-stratum/local-source two-sided loss-density iff

Date: 2026-06-29.

## Claim

Suppose residual hypotheses are known on a supplied `localSource`, and inside
an open neighborhood `Ulocal` of `x0` the source-rank stratum is contained in
that local source:

```text
Ulocal inter sourceStratum subset Ulocal inter localSource.
```

If four two-sided loss/density bounds are supplied in
`nhdsWithin x0 sourceStratum`, then there is an open base neighborhood `U`
such that actual p.13 regular-coordinate loss-density integrability over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

is equivalent to

```text
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem name:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_sourceStratum_bounds_locally_subset_localSource_two_sided_bounds
```

## Inputs Kept Explicit

- measurability of the source-rank stratum;
- an open `Ulocal` containing `x0`;
- the local coverage inclusion
  `Ulocal inter sourceStratum subset Ulocal inter localSource`;
- residual `AEMeasurable`, positivity, and `<= R^2` hypotheses on
  `mu.restrict localSource`;
- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`;
- `0 < R`, `0 < t`, `0 < cL`, `0 < CL`, `0 < dRho`, and `0 <= Dρ`;
- four supplied source-stratum-filter comparison bounds, uniform on the
  regular-coordinate ball.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

Independent xhigh review is recorded in
`review-a2-source-stratum-local-source-two-sided-loss-density-iff.md`.

`scripts/sorries`, `git diff --check`, the touched-file forbidden-marker scan,
and the direct axiom probe passed.  The axiom footprint for the theorem is
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

- No proof of comparison or residual hypotheses.
- No proof of the local coverage inclusion.
- No p.13 chart construction, chart coverage, source-prior transport,
  Jacobian or density theorem, product-measure transport, original-loss
  identification, normal-crossing, pole-order, or RLCT claim.
