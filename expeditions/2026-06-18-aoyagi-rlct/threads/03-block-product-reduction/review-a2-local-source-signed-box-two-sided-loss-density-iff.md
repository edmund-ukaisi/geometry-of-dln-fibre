# Review - A2 local-source signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: PASS after positivity-only weakening.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-local-source-signed-box-two-sided-loss-density-iff.md
statement-card-a2-local-source-signed-box-two-sided-loss-density-iff.md
```

## Controller Pre-Review

Pass with boundaries.

The theorem is a local supplied-bound socket.  Its proof derives residual
measurability from `hEdgeMatrix`, residual positivity from the new
positivity-only weighted signed-box monomial-lower helper, and then delegates
the iff to the previously landed local-source two-sided theorem.

The residual local boundedness hypothesis is explicit:

```text
residualSquareSum x <= Rreg^2
```

on `mu.restrict source`.  The theorem does not state or prove source coverage,
chart construction, Jacobian/source-density transport, original-loss
identification, normal crossings, pole order, or RLCT.

## Reviewer Results

Mencius flagged the first version because it called the finite residual-source
constructor, so its hypotheses already implied residual negative-power
integrability on the whole source.  The theorem was weakened by adding

```text
residualSquareSum_pos_ae_of_measure_map_signedBox_withDensity_monomialLower
residualSquareSum_pos_ae_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix
```

and by removing the signed-box critical inequalities, source-density
measurability/nonnegativity/upper-bound hypotheses, and residual signed-box
radius hypotheses from the two-sided wrapper.

Follow-up xhigh review PASS: the helper returns only residual positivity, and
the two-sided theorem no longer carries the signed-box critical/source-density
hypotheses that imply residual integrability.

Fermat also passed the Lean/API shape and built the file before the weakening.
The final controller build after the weakening passed.

Hygiene passed: focused `scripts/lb` build, `scripts/sorries`,
`git diff --check`, touched-file forbidden-marker scan, and direct axiom probes
for all three new public theorem names.  The axiom footprint is
`[propext, Classical.choice, Quot.sound]`.
