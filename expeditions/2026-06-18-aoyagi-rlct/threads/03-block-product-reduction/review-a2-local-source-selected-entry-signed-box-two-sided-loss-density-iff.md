# Review - A2 local-source selected-entry signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-local-source-selected-entry-signed-box-two-sided-loss-density-iff.md
statement-card-a2-local-source-selected-entry-signed-box-two-sided-loss-density-iff.md
```

## Controller Review

Pass with boundary.

The theorem is a specialization of the local-source signed-box two-sided iff.
It uses selected-entry algebra only to produce the monomial lower bound
required for residual positivity.  It does not assume the selected-entry
critical inequality, source-density nonnegativity, source-density upper bound,
or positive signed-box radii; those belong to the finite-side critical
integrability theorem, not to this iff socket.

Residual local boundedness and all four two-sided loss/density comparison
bounds remain explicit.

## Xhigh Review

Boole passed the theorem surface.  The review confirmed that the theorem uses
`SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds` only to
obtain `hres_lower_model`, then rewrites through `hresidual_eq`.  It ignores
the selected-entry source-density measurability, nonnegativity, and upper-bound
outputs.

The review also confirmed that the theorem does not assume selected-entry
critical inequalities, source-density bounds, positive signed-box radii, or
residual integrability.  The conclusion remains an iff against
`residualNegPowerIntegrableOn (U inter source) mu t`.

## Hygiene

Passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure
```

Passed:

```text
scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan passed.  Direct axiom probe for
the new theorem returned `[propext, Classical.choice, Quot.sound]`.
