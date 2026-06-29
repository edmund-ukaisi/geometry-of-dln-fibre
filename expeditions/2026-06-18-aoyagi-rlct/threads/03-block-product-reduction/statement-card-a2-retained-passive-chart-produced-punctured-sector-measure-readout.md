# Statement Card - A2 Retained-Passive Chart-Produced Punctured-Sector Measure Readout

Status: Lean theorem landed; focused and full builds passed; hygiene and
axiom probes passed; xhigh review PASS.

Reproduction:

```text
reproduction-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md
```

Review:

```text
review-a2-retained-passive-chart-produced-punctured-sector-measure-readout.md
```

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean
```

## Claim

For passive selected-entry Case 2 coordinates, after restricting the coordinate
domain to the open determinant-and-pivot-nonzero sector, the chart-produced
source measure has an exact inverse residual readout.  Pushing the restricted
coordinate measure forward by the source chart and then by the selected-entry
inverse residual readout gives the same measure as projecting the restricted
coordinate measure to its residual-coordinate factor.

The measure is chart-produced:

```text
Measure.map sourceChart (sourceMeasure.restrict V)
```

with `sourceMeasure` a measure on `eta x (center -> R)`.

## Lean

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
```

Helper:

```text
SelectedEntrySignedBox.CenterCoord.measurable_preimageOfPivotNeZero
```

## Proved

- There is an open set

```text
V = Udet inter {z | z.2 pivotNext != 0}
```

containing `z0`, assuming `z0.2 pivotNext != 0`.
- On `V`, `sourceChart z` lies in the retained-passive p.13 local source and
  `sourceReadback` recovers `retainedData z`.
- The chart-produced source pushforward restricts to the retained-passive
  local source as itself.
- The source-side inverse residual readout is measurable.
- The inverse residual readout agrees with `Prod.snd` after composition with
  `sourceChart`, almost everywhere for `sourceMeasure.restrict V`.
- Therefore

```text
Measure.map inverseReadout
  (Measure.map sourceChart (sourceMeasure.restrict V))
=
Measure.map Prod.snd (sourceMeasure.restrict V).
```

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of passive fields `A1passive`, `F2`, `A3passive`, `Ctop`, and
  `F3`.
- Basepoint determinant units for `Ctop z0.1` and `A1passive z0.1`.
- The basepoint nonzero-pivot condition `z0.2 pivotNext != 0`.
- Fixed-base complement data `U0, hU0`.
- A coordinate-domain measure `sourceMeasure`.
- Borel/measurable structure on the fixed-base edge-family target, as in the
  existing support theorem.

## Cited

Aoyagi pp. 10-13 supply the retained-passive block substitutions and the p.13
product-difference variables.  The measure theorem itself is finite-coordinate
and measure-theoretic bookkeeping over already-proved source/readback and
selected-entry inverse lemmas.

## Deferred

- Determinant-chart Haar transport.
- Raw/source Haar theorem.
- External/original source-prior comparison.
- Passive Jacobian formula for a source prior.
- Selected-entry source-image equality or source-rank coverage.
- Normal crossings, pole order, and RLCT extraction.

## Nonclaims

This card does not call `sourceMeasure` an Aoyagi prior, does not remove a full
determinant-chart Haar `hmap` field, and does not identify the selected-entry
source density with the passive determinant-chart Jacobian.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure
```

Post-recovery verification also passed:

```text
scripts/lb DLNFibre
scripts/sorries
git diff --check
touched Lean-file forbidden-marker scan
direct axiom probes: [propext, Classical.choice, Quot.sound]
```

The builds replayed only pre-existing warning noise from unrelated modules.
