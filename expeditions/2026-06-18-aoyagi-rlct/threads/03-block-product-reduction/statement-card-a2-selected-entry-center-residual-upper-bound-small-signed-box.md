# Statement Card - A2 selected-entry center residual upper bound on small signed boxes

Date: 2026-06-29.

## Claim

For a center-indexed selected-entry chart, if every center coordinate satisfies

```text
|y_i| <= delta
```

and

```text
delta^2 * (1 + #(center.erase pivot) * delta^2) <= R^2,
```

then the selected-entry residual square-sum is at most `R^2`.  Consequently,
on any signed box whose radii are all `<= delta`, the same residual upper bound
holds pointwise, a.e. for the unweighted signed-box measure, and a.e. for the
selected-entry weighted source-box measure.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

Main lemmas:

```text
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_abs_le
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_mem_signedBoxSet
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_signedBox_of_smallBox
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_withDensity_sourceDensity_of_smallBox
```

## Proved

- The selected-entry center residual factors as the pivot square times the
  normalized non-pivot square-sum.
- Uniform coordinate bounds imply a residual upper bound.
- Signed-box membership supplies those coordinate bounds when `Rres_i <= delta`.
- The residual upper bound holds a.e. for the signed-box measure.
- The residual upper bound also holds a.e. after weighting by
  `sourceDensity pivot`, via absolute continuity.

## Assumed

- A nonnegative bound `delta`.
- Small-box hypotheses `Rres_i <= delta`.
- The explicit scalar inequality
  `delta^2 * (1 + #(center.erase pivot) * delta^2) <= R^2`.

## Cited

None in this theorem.

## Deferred

No retained-passive measure-map discharge yet; no selected-entry
negative-power integrability or critical inequality; no source-prior or
Jacobian transport; no source/image or source-rank coverage theorem; no normal
crossings, pole order, or RLCT extraction.

## Status

Focused Lean build passed for
`DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure`.  `scripts/sorries`,
`git diff --check`, touched Lean-file forbidden-marker scan, direct axiom
probe, and Euclid the 2nd xhigh read-only review passed.  The axiom footprint
is `[propext, Classical.choice, Quot.sound]`.
