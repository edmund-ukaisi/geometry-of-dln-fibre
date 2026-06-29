# Statement Card - A2 source-stratum bounds local-source finite integral

Date: 2026-06-29.

## Claim

The p. 13 regular-coordinate finite-integral handoff can use loss and density
bounds stated on the source-rank stratum while using residual positivity and
residual negative-power integrability supplied on a local source, provided an
explicit open neighborhood identifies the relevant part of the source-rank
stratum as lying inside that local source.

## Source / Proof Basis

Aoyagi PDF p. 13 supplies the regular-coordinate split into residual variables
and regular variables.  This theorem is not a new p. 13 algebra calculation; it
is the measure-locality bridge needed to combine source-stratum comparison
estimates with retained-passive local-source residual hypotheses.

Lean dependencies:

```text
exists_open_ae_restrict_source_prod_p13RegularCoordinates_loss_density_bounds
residualSourceHypotheses_mono
lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Declaration:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
```

## Inputs Kept Explicit

- source-stratum measurability;
- open neighborhood `Ulocal` containing the base point;
- local inclusion `Ulocal cap sourceStratum subset Ulocal cap localSource`;
- residual positivity and residual negative-power integrability on
  `localSource`;
- source-stratum filter lower bound for the loss;
- source-stratum filter nonnegativity and upper bound for the density.

## Nonclaims

No source-rank coverage theorem, no selected-entry chart image equality, no
residual coordinate readout along a selected-entry chart, no source-prior or
Jacobian transport, no analytic atlas, no normal crossings, no pole order, and
no RLCT statement is proved.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

Forbidden-marker and whitespace checks passed:

```text
cd lean
scripts/sorries
cd ..
git diff --check
```

An xhigh review passed with no findings:
`review-a2-source-stratum-bounds-local-source-finite-integral.md`.
