# Reproduction - A2 Case 2 source-chart chart-piece density readback domination

Date: 2026-07-01.

Status: pen-and-paper check for the concrete chart-piece bounded-density
readback handoff.

## Question

Suppose a measurable source-side chart piece `chartPiece` carries an external
measure whose restriction is a bounded-density perturbation of the
chart-produced source reference:

```text
externalMeasure.restrict chartPiece =
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict chartPiece

density <= c
  almost everywhere for
  (Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece.
```

If `V` is the local passive-theta source-chart domain with readback left
inverse, what does the readback of this restricted external measure satisfy?

## Calculation

The local source-chart package gives:

```text
readback (sourceChart theta) = theta   for theta in V,
Set.InjOn sourceChart V,
ContinuousOn sourceChart V.
```

Thus the readback is a.e.-measurable on the chart-produced source reference.
The bounded-density identity first gives domination on the source side:

```text
externalMeasure.restrict chartPiece
  <= c • Measure.map sourceChart (thetaReference.restrict V).
```

Mapping by `readback` preserves scalar domination, so

```text
Measure.map readback (externalMeasure.restrict chartPiece)
  <= c • Measure.map readback
       (Measure.map sourceChart (thetaReference.restrict V)).
```

The source-reference readback identity reduces the right side to
`c • thetaReference.restrict V`.  If `V ⊆ W`, then
`thetaReference.restrict V <= thetaReference.restrict W`, hence the target
domination is

```text
Measure.map readback (externalMeasure.restrict chartPiece)
  <= c • thetaReference.restrict W.
```

The existing generic theorem

```text
aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
```

packages exactly this calculation.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
```

## Boundary

The theorem assumes the bounded-density identity and bound.  It does not prove
that the original source prior or original volume satisfies such an identity,
does not prove chart-image coverage, does not transport Haar measure, and does
not prove normal crossings, pole order, or RLCT extraction.
