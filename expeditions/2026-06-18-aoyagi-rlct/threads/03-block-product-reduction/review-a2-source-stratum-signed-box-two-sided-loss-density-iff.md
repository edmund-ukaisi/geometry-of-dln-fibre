# Review - A2 source-stratum signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-source-stratum-signed-box-two-sided-loss-density-iff.md
statement-card-a2-source-stratum-signed-box-two-sided-loss-density-iff.md
```

## Controller Review

Pass with boundaries.

The theorem is a source-rank-stratum wrapper over the local-source signed-box
two-sided theorem.  It keeps residual boundedness and all loss/density
comparison bounds explicit.  It does not add signed-box critical inequalities
or source-density upper/nonnegativity hypotheses, so residual integrability is
not hidden in the assumptions.

## Xhigh Review

Anscombe passed the theorem surface.  The review confirmed that the wrapper
assumes source-stratum measurability, measurable edge matrices, sourceChart
a.e. measurability, the pushforward identity for `mu.restrict sourceStratum`,
`hcres` and the monomial residual lower bound, explicit `hle_source`,
`[SFinite nu] [nu.IsAddHaarMeasure]`, comparison constants, and the four
source-stratum two-sided bounds.  It delegates directly to the local-source
theorem with `source := sourceStratum` and does not assume signed-box critical
inequalities, source-density nonnegativity, or source-density upper bounds.

## Hygiene

Passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan passed.  Direct axiom probe for the
new source-stratum wrapper returned `[propext, Classical.choice, Quot.sound]`.
