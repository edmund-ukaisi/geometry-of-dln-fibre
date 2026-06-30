# Reproduction - A2 Original-Prior Density From Unweighted Domination

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is a source-prior measure
adapter, not a source-chart transport theorem.

## Question

Aoyagi's statistical setup uses a smooth compactly supported prior density
`phi` with `phi(w*) > 0` near the true parameter. Once an unweighted local
source measure has been compared with a chart-produced reference measure, can
the weighted prior be compared without adding a new analytic assumption?

## Calculation

Let `mu` be the unweighted original/source measure on a source space, let `nu`
be the chart-produced reference measure, and let `s` be the local source
piece. Assume

```text
mu.restrict s <= c • nu
```

and let `f : source -> ENNReal` be the prior density. If the prior is locally
bounded on the same piece,

```text
f <= C    a.e. with respect to mu.restrict s,
```

then

```text
(mu.withDensity f).restrict s
  = (mu.restrict s).withDensity f
  <= C • mu.restrict s
  <= C • (c • nu)
  = (C * c) • nu.
```

For a real-valued prior density `rho : source -> Real`, the same calculation
applies to `f x = ENNReal.ofReal (rho x)` using

```text
rho <= K  ==>  ENNReal.ofReal rho <= ENNReal.ofReal K.
```

## Source Fidelity

Aoyagi pp. 5 and 8 support the existence of a smooth prior density and the
use of local boundedness once a valid coordinate-change identity is in place.
They do not supply the project-specific identity

```text
unweighted original/source measure restricted to s
  <= c • chart-produced source-image measure.
```

Aoyagi pp. 10-13 support the p.13 Schur/product algebra already formalized in
the retained-passive coordinate files. They do not by themselves identify the
original prior with the retained-passive chart-produced measure.

## Lean Target

Add the ambient flattened-coordinate prior module:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalPrior.lean

originalCoordinateVolume
originalCoordinatePrior
originalCoordinatePrior_restrict_le_smul_of_ae_le

measurable_canonicalCoord
measurable_canonicalCoord_symm
originalTupleVolume
originalTupleVolume_map_canonicalCoord
originalTuplePrior
originalTuplePrior_restrict_le_smul_of_ae_le
```

Here `originalCoordinateVolume d` is product Lebesgue measure on
`RepCoord d -> Real`, the coordinate space used by `canonicalCoord d`.  This
names an original ambient measure independently of any retained-passive
source-chart pushforward.

The tuple-side measure is

```text
originalTupleVolume d
  = Measure.map (canonicalCoord d).symm (originalCoordinateVolume d),
```

so it lives on the original matrix tuple type `Tuple (k := Real) d` without
being defined through an Aoyagi chart.  The coordinate map and its inverse are
measurable, and Lean proves

```text
Measure.map (canonicalCoord d) (originalTupleVolume d)
  = originalCoordinateVolume d.
```

The tuple-side prior and bounded-density domination are the same elementary
with-density calculation over `originalTupleVolume d`.

Also add two reusable helpers to
`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`:

```text
restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le

restrict_withDensity_ofReal_le_smul_of_restrict_le_smul_of_ae_le
```

These helpers turn a future unweighted Haar/chart transport theorem into the
corresponding prior-weighted domination theorem.  Finiteness of the scalar
bound is not hidden in these helpers; downstream integrability transfers must
still supply it when required.

## Nonclaims

No theorem transports `originalCoordinateVolume`, `originalTupleVolume`, or
the corresponding priors through an Aoyagi source chart.  No theorem proves
the unweighted Haar/chart transport hypothesis. No source-image equality,
source-rank coverage, determinant/raw-order Haar transport, normal crossings,
pole order, or RLCT extraction is proved.
