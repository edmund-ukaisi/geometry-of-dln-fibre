# Review - A2 Retained-Passive Chart-Produced Punctured-Sector Measure Readout

Date: 2026-06-29.

Reviewer: Hubble the 3rd, xhigh read-only.

Verdict: PASS.

## Scope Checked

Artifacts:

```text
reproduction-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md
statement-card-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md
```

The review checked the Aoyagi-only boundary, the current Lean APIs in
`RetainedPassiveCase2PassiveSelectedEntrySource.lean` and
`RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`, and the measure
trichotomy:

```text
chart-produced sector measure
determinant-chart Haar
external/original source prior
```

## Findings

The artifacts stay inside the chart-produced sector-measure lane.  They do not
identify the coordinate-domain measure with determinant-chart Haar or with
Aoyagi's original source prior.

The pivot-nonzero condition is correctly kept as part of the sector.  The
pointwise input theorem only proves inverse readout under
`z.2 pivotNext != 0`, and the measure statement restricts to the open set

```text
Udet inter {z | z.2 pivotNext != 0}.
```

The support claim is appropriately limited to the chart-produced source
pushforward

```text
Measure.map sourceChart (sourceMeasure.restrict V).
```

## Lean Cautions Addressed

The reviewer warned that support on the smaller punctured set should reuse the
generic support lemma or a restriction argument.  The landed proof reuses the
generic support lemma directly over the smaller open set.

The reviewer also warned that global measurability of the inverse readout may
need explicit finite-coordinate lemmas.  The landed proof adds

```text
SelectedEntrySignedBox.CenterCoord.measurable_preimageOfPivotNeZero
```

and combines it with the existing fixed-base residual-coordinate measurability
lemma.

## Nonclaims

No determinant-chart Haar transport, raw/source Haar theorem,
external/original source-prior comparison, passive Jacobian formula,
selected-entry source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction is reviewed or claimed here.
