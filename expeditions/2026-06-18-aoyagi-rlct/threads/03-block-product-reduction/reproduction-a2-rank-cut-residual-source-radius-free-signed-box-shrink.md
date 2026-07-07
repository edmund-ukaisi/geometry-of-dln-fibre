# A2 rank-cut residual-source radius-free signed-box shrink

## Object-level calculation

The fixed-radius source-cylinder shrink proves the strict rank-cut
residual-source package when a chosen signed box contains the basepoint
selected-entry coordinate:

```text
z0.1.yNext in signedBoxSet Rres.
```

For the final rank-cut residual-source package, the selected-entry radii are
not part of the returned data.  We can therefore choose them before applying
the fixed-radius theorem.  The finite-coordinate signed-box lemma gives

```text
exists Rres, (forall i, 0 < Rres i) and
  z0.1.yNext in signedBoxSet Rres.
```

Applying the fixed-radius theorem to this chosen `Rres` returns open sets

```text
V subset W subset G
```

and the same rank-cut residual-source package.  Since neither the final
statement nor the returned package exposes the `Rres`-dependent source
cylinder, reference source, or coordinate source measure, the radii can remain
proof-local.

## Lean artifact

The new declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

It calls:

```text
SelectedEntrySignedBox.CenterCoord.exists_pos_mem_signedBoxSet
```

and then the fixed-radius theorem:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_z0_yNext_mem_signedBox_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
```

## Boundary

This removes the explicit `Rres`, positive-radius, and basepoint-in-signed-box
inputs from the rank-cut residual-source API.  It is a wrapper, not a new
analytic theorem.  It is honest only because the conclusion does not expose
the selected-entry source cylinder or any `Rres`-dependent measure.

It does not prove source-density positivity, prior-density strict upper
bounds, determinant/raw Haar transport, source-prior transport, source-rank or
atlas coverage, normal crossings, pole order, or RLCT extraction.
