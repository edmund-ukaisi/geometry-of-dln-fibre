# Review - A2 selected-entry center residual upper bound on small signed boxes

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean lemmas:

```text
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_abs_le
SelectedEntrySignedBox.CenterCoord.residual_le_sq_of_mem_signedBoxSet
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_signedBox_of_smallBox
SelectedEntrySignedBox.CenterCoord.residual_le_sq_ae_withDensity_sourceDensity_of_smallBox
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

Documentation:

```text
reproduction-a2-selected-entry-center-residual-upper-bound-small-signed-box.md
statement-card-a2-selected-entry-center-residual-upper-bound-small-signed-box.md
```

## Controller Review

Pass with boundary.

The pointwise theorem uses the exact selected-entry square-sum formula and
keeps the smallness condition explicit as

```text
delta^2 * (1 + #(center.erase pivot) * delta^2) <= R^2.
```

The signed-box theorem only converts membership in `signedBoxSet Rres` into
coordinate bounds, under `Rres_i <= delta`.  The a.e. signed-box theorem uses
only support of the restricted product measure.  The weighted a.e. theorem
uses only absolute continuity of `withDensity`.

No theorem in this slice proves residual integrability, source-prior
transport, retained-passive chart production, normal crossings, pole order, or
RLCT.

## Xhigh Review

Euclid the 2nd passed the theorem surface.

The review confirmed that the pointwise bound uses the correct selected-entry
factorisation, that signed-box membership is only used to obtain coordinate
absolute-value bounds, that the weighted a.e. theorem uses only
`withDensity_absolutelyContinuous`, and that the names/statements are precise
and reusable.

No line-specific concerns were reported.

## Hygiene

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
```

Passed:

```text
scripts/sorries
git diff --check
touched Lean-file forbidden-marker scan
direct axiom probe
```

The direct axiom probe returned `[propext, Classical.choice, Quot.sound]` for
the new selected-entry residual upper-bound lemmas.
