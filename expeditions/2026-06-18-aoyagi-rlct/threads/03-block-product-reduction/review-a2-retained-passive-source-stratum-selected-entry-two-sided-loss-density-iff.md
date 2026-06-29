# Review - A2 retained-passive source-stratum selected-entry two-sided loss-density iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md
statement-card-a2-retained-passive-source-stratum-selected-entry-two-sided-loss-density-iff.md
```

## Controller Review

Pass with boundary.

The theorem uses the retained-passive local source as the residual chart source
and the source-rank stratum as the comparison-bound/final-integral source.
The bridge between them is the explicit retained-passive self-base local
coverage theorem, not a signed-box source/image equality.

The selected-entry signed-box data is used only to prove residual positivity
on `mu.restrict localSource` from the monomial lower bound.  Residual
boundedness and all four source-stratum two-sided comparison bounds remain
explicit.  The theorem does not assume selected-entry critical inequalities,
positive signed-box radii, source-density upper/nonnegativity hypotheses,
residual integrability, original source-prior transport, normal crossings,
pole order, or RLCT.

## Xhigh Review

Cicero the 2nd passed the theorem surface.

The review confirmed that source-stratum coverage is handled through
`exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase`
and then passed to the generic source-stratum/local-source bridge.  The theorem
does not pretend that the signed-box chart directly covers the source-rank
stratum.

The review also confirmed that residual measurability is derived from
`Continuous Cedge`, residual positivity is derived from the selected-entry
monomial lower bound plus `hresidual_eq`, `hmap`, and `hsourceChart`, residual
boundedness remains explicit, `hbase` is used only for retained-passive local
coverage, and no `[SFinite mu]` is introduced.

## Hygiene

Passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
```

Passed:

```text
scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan passed.  Direct axiom probe for
the new theorem returned `[propext, Classical.choice, Quot.sound]`.
