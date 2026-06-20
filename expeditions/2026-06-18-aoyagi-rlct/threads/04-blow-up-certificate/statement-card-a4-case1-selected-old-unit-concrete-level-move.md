# Statement card - A4 Case 1 selected-old Unit concrete level move

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Name:

- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.of_sameDomain_case1SelectedOldLevelMove`

## Statement

Lean now instantiates the selected-old `Unit` chart-family boundary using the
concrete same-domain recurrence post-state:

```text
post = pre.case1SelectedOldLevelMove s0 k0,
u = pre.var s0 k0,
baseStep = pre.erasedStep s0 k0.
```

Given a same-domain Case 1(1) selected-old boundary stated over `pre.level`
and a supplied finite Case 1 chart-family boundary, the theorem returns a
`Case1SelectedOldUnitSuppliedChartFamilyBoundary` with these concrete choices.

## Source Role

This is the Case 1(1) selected-old `Unit` chart wrapper for the concrete
recurrence level move.  It packages the recurrence-state witness with the
finite chart-family assumption; it does not add a new chart or transition
calculation.

## Proved

- The concrete lowered recurrence boundary can be used as the `lowered` field
  of the Unit chart-family boundary.
- The supplied `Case1CenterChartFamilyBoundary` fills the chart-family field.
- All existing Unit-boundary projections apply to the concrete post-state.

## Not Proved

- No construction of the selected-old chart from raw coordinates.
- No proof of chart regularity or transition regularity from coordinates.
- No inference of `(s0,k0)` from the `Unit` finite-center token.
- No domain advancement to `(S,J+1)`.
- No Case 1(2) displayed pivot, `Q/P`, chart coverage, Jacobian, normal
  crossings, RLCT extraction, or full transition invariant.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-unit-concrete-level-move-a4.md`.
- Review artifact:
  `review-case1-selected-old-unit-concrete-level-move-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
