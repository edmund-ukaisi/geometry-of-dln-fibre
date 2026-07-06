# A2 Source-image Chart-piece Subset Bridges

## Source Calculation

For the with-following Case 2 p.13 source chart, the useful local image
equality has the form

```text
sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V.
```

This equality says that a point is in the local source-chart image precisely
when it is in the named p.13 source set and its readback lands in the chosen
theta neighborhood.  Therefore, for any chart piece,

```text
chartPiece subset p13SourceSet
chartPiece subset readback ⁻¹' V
```

imply

```text
chartPiece subset sourceChart '' V.
```

The rank-cut variant is the same set calculation with an extra source-rank
condition:

```text
sourceChart '' (V ∩ rankEq) =
  (p13SourceSet ∩ readback ⁻¹' V) ∩ sourceStratum.
```

Then the three inclusions

```text
chartPiece subset p13SourceSet
chartPiece subset readback ⁻¹' V
chartPiece subset sourceStratum
```

give

```text
chartPiece subset sourceChart '' (V ∩ rankEq).
```

These are the set-theoretic adapters needed by downstream wrappers that still
ask for `chartPiece subset sourceChart '' V`.

## Lean Targets

The plain image-subset adapter is:

```text
chartPiece_subset_sourceChart_image_of_subset_p13_readback
```

The rank-cut adapter is:

```text
chartPiece_subset_sourceChart_image_rankCut_of_subset_p13_readback_sourceStratum
```

Both are in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

## Boundary

These lemmas prove no image equality.  They consume an already-proved local
image equality and perform only subset algebra.  They do not prove source
coverage, source-rank coverage, source-prior transport, determinant/raw Haar
transport, normal crossings, pole order, or RLCT extraction.

## Kill Conditions

- Kill any use that applies the plain adapter to the plain endpoint chart
  without a supplied image equality.
- Kill any use that drops the readback-preimage condition.
- Kill any use that treats chart-piece containment in one local image as global
  source-rank coverage.
