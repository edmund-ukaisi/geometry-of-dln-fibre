# Reproduction - A2 Original Tuple Volume Haar Normalization

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is coordinate/Haar
infrastructure for comparing future source-chart measures. It is not a
source-chart transport theorem.

## Question

The original tuple measure is

```text
originalTupleVolume d
  := (canonicalCoord d)^{-1}_* volume
```

where `volume` is product Lebesgue measure on the flattened coordinate space
`RepCoord d -> R`. Is this measure an additive Haar measure on
`Tuple (k := R) d`, and how does it compare to any other additive Haar measure
on the same tuple space?

## Calculation

The flattened coordinate space is the finite real vector space

```text
RepCoord d -> R,
```

where

```text
RepCoord d = Sigma i : Fin N, Fin (d i.succ) x Fin (d i.castSucc).
```

Product Lebesgue measure on a finite real coordinate space is an additive Haar
measure. Thus

```text
originalCoordinateVolume d = volume
```

is Haar.

The map `canonicalCoord d` is entry-flattening:

```text
(canonicalCoord d A) <i,r,c> = A_i(r,c).
```

This map is not merely a set equivalence. It is linear, because addition and
scalar multiplication of matrix tuples are entrywise:

```text
canonicalCoord d (A + B) = canonicalCoord d A + canonicalCoord d B,
canonicalCoord d (a • A) = a • canonicalCoord d A.
```

Finite-dimensional linear maps between the tuple space and the flattened
coordinate space are continuous, so `canonicalCoord d` upgrades to a continuous
linear equivalence. Haar measure is preserved by pushforward along a continuous
linear equivalence. Therefore the inverse pushforward

```text
Measure.map (canonicalCoord d).symm (originalCoordinateVolume d)
```

is an additive Haar measure on the tuple space. This is exactly
`originalTupleVolume d`.

Finally, Haar uniqueness on locally compact second countable additive groups
says that if `nu` is any additive Haar measure on `Tuple (k := R) d`, then

```text
originalTupleVolume d
  = addHaarScalarFactor (originalTupleVolume d) nu • nu.
```

The scalar is positive because both measures are Haar. Since the scalar lives
in `R>=0`, its coercion to `R>=0∞` is finite.

## Source Fidelity

Aoyagi p.13 works with ordinary finite-dimensional matrix coordinate spaces.
This reproduction only records the standard finite-dimensional Lebesgue/Haar
normalization fact for the original coordinate measure. It does not introduce a
new analytic citation and does not identify the original measure with any
retained-passive chart-produced source measure.

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalPriorHaar.lean

canonicalCoordLinearEquiv
canonicalCoordLinearEquiv_apply
canonicalCoordLinearEquiv_symm_apply
isAddHaarMeasure_originalCoordinateVolume
isAddHaarMeasure_originalTupleVolume
originalTupleVolume_eq_addHaarScalarFactor_smul
originalTupleVolume_addHaarScalarFactor_pos
```

The file reuses the existing matrix topology/Borel bridge from
`ChartTopology.lean`.  The remaining local-compactness bridge needed by
Mathlib's Haar uniqueness theorem is proof-local in the scalar-comparison
theorem, so no duplicate global matrix topology/Borel instances are exported.

## Kill Conditions

- If `canonicalCoord d` failed to be linear, the inverse pushforward would not
  inherit Haar measure by the continuous-linear-equivalence API.
- If the tuple space did not carry the product Borel/topological vector-space
  structure, Haar uniqueness would not apply.
- If a later source-chart theorem silently assumes the scalar is `1`, this
  calculation would be misused. The correct general comparison is finite
  scalar equivalence, not exact equality under arbitrary Haar normalization.

## Nonclaims

No theorem here identifies `originalTupleVolume` or `originalEdgeFamilyVolume`
with a retained-passive or selected-entry chart-produced source-image measure.
No theorem proves chart-piece equality, readback domination,
Haar/Jacobian transport for an Aoyagi chart, source-rank coverage, normal
crossings, pole order, or RLCT extraction.
