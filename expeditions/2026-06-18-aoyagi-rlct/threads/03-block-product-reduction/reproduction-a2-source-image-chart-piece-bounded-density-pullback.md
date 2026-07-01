# Reproduction - A2 Source-image Chart-piece Bounded-density Pullback

Date: 2026-07-01.

Status: pen-and-paper check completed before Lean; Lean implementation proved
and verified.

## Question

The existing source-image bounded-density pullback theorem handles the whole
local image `sourceChart '' V`.  The Aoyagi finite-integral sockets, however,
work with an arbitrary measurable chart piece

```text
chartPiece subset sourceChart '' V.
```

Can the same bounded-density pullback be stated directly for such a measurable
piece?

## Calculation

Let

```text
sourceBase = Measure.map sourceChart (thetaReference.restrict V).
```

Assume the restricted external measure is a bounded-density perturbation of
`sourceBase` on a measurable `chartPiece`:

```text
externalMeasure.restrict chartPiece =
  (sourceBase.withDensity density).restrict chartPiece,
density <= c  sourceBase.restrict chartPiece-a.e.
```

Then the standard with-density restriction bound gives

```text
(sourceBase.withDensity density).restrict chartPiece <= c • sourceBase.
```

Since `readback` is a.e.-measurable for `sourceBase`, and the left side is
absolutely continuous with respect to `sourceBase`, `readback` is also
a.e.-measurable for the restricted bounded-density piece.  Mapping the
domination by `readback` gives

```text
Measure.map readback ((sourceBase.withDensity density).restrict chartPiece)
  <= c • Measure.map readback sourceBase.
```

The local left-inverse theorem gives

```text
Measure.map readback sourceBase = thetaReference.restrict V.
```

Replacing the bounded-density piece by `externalMeasure.restrict chartPiece`
using the supplied equality yields

```text
Measure.map readback (externalMeasure.restrict chartPiece)
  <= c • thetaReference.restrict V.
```

No support or coverage statement about `chartPiece` is needed for this measure
inequality; containment in the actual image is used by downstream Aoyagi
wrappers for right-inverse and p.13 support obligations.

## Lean Target

Add a generic theorem to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity
```

and the convenience version discharging readback a.e.-measurability from a
continuous injective local source chart:

```text
measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn
```

## Nonclaims

No original/source prior density identity is proved.  No source-image coverage,
source-rank coverage, Haar transport, Jacobian formula, normal crossings, pole
order, or RLCT extraction is proved.
