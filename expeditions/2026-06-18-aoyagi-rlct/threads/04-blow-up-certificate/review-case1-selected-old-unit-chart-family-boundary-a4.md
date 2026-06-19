# Review - A4 Case 1(1) Selected-Old Unit Chart-Family Boundary

Status: reviewed by controller and independent xhigh reviewers; pass.

## Math Review

The package is a narrow supplied interface for Aoyagi Case 1(1), not a chart
production theorem. It combines:

- `Case1SelectedOldLoweredRecurrenceBoundary`, which supplies the selected-old
  lowered recurrence and same-domain exponent update;
- `Case1CenterChartFamilyBoundary`, which supplies chart regularity and
  transition regularity for every generator in the finite Case 1 center.

The source-label facts still come from the carried first-jump/lowered
recurrence data, not from the finite `Unit` token. The selected-old token is
only the generator

```text
Sum.inl () : Case1CenterGenerator.
```

It is kept separate from Aoyagi Case 1(2)'s displayed top-left row-strip pivot

```text
Sum.inr (J+1,J+1) : Case1CenterGenerator.
```

## Lean/API Review

The boundary stays over the same domain `(S,J)`: both recurrence states are
`IntroducedLabelRecurrenceState L n S J R`, and the exponent projection
returns `IntroducedLabelExponentCertificates L n S J ...`.

The selected-old membership projection uses only
`case1_selectedOld_mem_center`; it does not import the source column bound
needed for displayed-pivot membership. The value-set, divisibility, and finite
center ideal projections all use the `Sum.inl ()` selected-old token.

The transition projections quantify over any finite Case 1 center generator.
This is broader than the older displayed-pivot-specific convenience
projections, but it is exactly the existing contract of
`Case1CenterChartFamilyBoundary.transition_regular_of_mem`, which supplies
regularity for every pair of finite center generators.

## Caveats

- The theorem `selectedOld_selectedEntryChartMap_value_mem` is pure finite
  center algebra packaged in the namespace; it does not use the boundary data
  and should not be read as constructing the selected-old source chart.
- The prose identification of `u` with the selected old denominator
  `u_(s0,k0)` is source-facing intent. Lean only treats `u` as the scalar
  shared by the supplied lowered recurrence boundary and selected-entry map.
- No chart construction, affine atlas, chart coverage, coordinate-derived
  regularity, raw source pullback, chart-produced post-data, `Q/P` transition,
  Jacobian accounting, normal crossings, RLCT extraction, or full transition
  invariant is proved.

## Independent xhigh Review

Independent xhigh reviewers found no blockers. They confirmed that the package
is a conservative wrapper; that the domain remains `(S,J)` rather than
`(S,J+1)`; that `Sum.inl ()` is not confused with the displayed row-strip pivot
`Sum.inr (J+1,J+1)`; and that all projected facts are direct re-exports of
supplied chart-family data, existing finite selected-entry algebra, or the
lowered recurrence boundary.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
