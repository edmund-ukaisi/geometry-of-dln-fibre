# Review - A2 Original Tuple Volume API

Date: 2026-06-30.

Reviewer: xhigh sidecar `Curie the 2nd`.

## Verdict

PASS for target shape, with a strict nonclaim boundary.

Defining

```text
originalTupleVolume d
  = Measure.map (canonicalCoord d).symm (originalCoordinateVolume d)
```

is mathematically honest because `Tuple (k := ℝ) d` is the actual matrix-tuple
parameter space and `canonicalCoord d` is the canonical entry-flattening
equivalence.  This is useful scaffolding for the original source-prior
frontier, but it is only a relabeling of the original coordinate measure.  It
does not transport the measure through an Aoyagi source chart.

## API Guidance Used

The least overclaiming useful declarations are:

```text
measurable_canonicalCoord
measurable_canonicalCoord_symm
originalTupleVolume
originalTupleVolume_map_canonicalCoord
originalTuplePrior
originalTuplePrior_restrict_le_smul_of_ae_le
```

The tuple-side prior should be defined by `withDensity` on
`originalTupleVolume`, not as an opaque mapped prior measure.

The `Matrix` measurable-space instance needed for tuple measurability should
not force `OriginalPrior.lean` to import the full chart-topology layer.  The
implementation therefore puts that instance in the lightweight
`MatrixMeasurable.lean` module and has `ChartTopology.lean` import it.

## Nonclaims

No theorem here identifies the original tuple measure with a retained-passive
or selected-entry chart-produced source-image measure.  No theorem proves
source-chart image equality, Haar/Jacobian transport, source-rank coverage,
normal crossings, pole order, or RLCT extraction.
