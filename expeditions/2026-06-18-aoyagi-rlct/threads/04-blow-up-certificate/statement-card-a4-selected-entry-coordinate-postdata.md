# Statement card - A4 selected-entry coordinate postdata

Date: 2026-06-24.

## Claim

For the finite selected-entry chart-family certificate, the unique chart
coordinate is the exceptional coordinate.  At a source chart point it is `u`;
at a transition-generated target chart point it is `u` multiplied by the
source chart's normalized target entry.

## Source Status

Aoyagi PDF pp. 19-22 display the Case 2 top-left selected-entry chart, where
the pivot entry is the exceptional coordinate `u` and the other selected
center entries are `u` times normalized coordinates.  The arbitrary all-pivot
finite chart family used in Lean is a finite selected-entry generalization; it
is not a claim that Aoyagi prints every pivot chart.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-selected-entry-coordinate-postdata-a4.md`.

Review:
`review-selected-entry-coordinate-postdata-a4.md`.

Verdict: qualified pass after source-wording correction.  The checker required
the distinction between Aoyagi's displayed top-left chart and Lean's all-pivot
finite generalization, reserved the word overlap for nonzero denominator
statements, and kept the coordinate index explicit as `(0 : Fin 1)`.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.

Generic selected-entry theorems:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq
```

Case 2 source-selected wrappers:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq_sourceSelected
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq_sourceSelected
```

The generic proofs are definitional.  The Case 2 wrappers are specializations
through the existing residual-block chart-family abbreviations.

## Nonclaims

This proves only finite coordinate postdata.  It does not prove analytic chart
domains, chart coverage, transition regularity, source production of successor
matrices or suffixes, analytic Jacobian/volume-form compatibility, global
normal crossings, termination, pole order, or RLCT extraction.
