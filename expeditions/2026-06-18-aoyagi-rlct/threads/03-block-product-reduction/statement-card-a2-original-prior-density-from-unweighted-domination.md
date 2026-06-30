# Statement Card - A2 Original-Prior Density From Unweighted Domination

## Claim

If an unweighted local original/source measure is dominated by a scalar
multiple of a chart-produced reference measure, then weighting it by a locally
bounded prior density preserves domination, with the scalar multiplied by the
prior-density bound.  Later finite-integral applications still supply the
needed scalar finiteness hypotheses.

Public Lean names:

```text
originalCoordinateVolume
originalCoordinatePrior
originalCoordinatePrior_restrict_le_smul_of_ae_le

measurable_canonicalCoord
measurable_canonicalCoord_symm
originalTupleVolume
originalTupleVolume_map_canonicalCoord
originalTuplePrior
originalTuplePrior_restrict_le_smul_of_ae_le

restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le

restrict_withDensity_ofReal_le_smul_of_restrict_le_smul_of_ae_le
```

## Inputs Used

- a measurable local source piece `s`;
- an unweighted domination hypothesis `mu.restrict s <= c • nu`;
- a local a.e. upper bound `f <= C` with respect to `mu.restrict s`;
- for the real-valued helper, a bound `density <= K` and monotonicity of
  `ENNReal.ofReal`.

## Output

The original-coordinate module defines product Lebesgue measure on the
flattened parameter coordinate space:

```text
originalCoordinateVolume d : Measure (RepCoord d -> Real)
```

and its prior-weighted variant:

```text
originalCoordinatePrior d density
```

with the local bounded-density domination:

```text
(originalCoordinatePrior d density).restrict s
  <= ENNReal.ofReal K • (originalCoordinateVolume d).restrict s.
```

The theorem records domination.  Later finite-integral transfer theorems must
still carry the needed finite-scalar hypotheses.

The module also defines the same original measure on the matrix tuple space:

```text
originalTupleVolume d : Measure (Tuple (k := Real) d)
```

by pushing `originalCoordinateVolume d` through `(canonicalCoord d).symm`.
The coordinate map and its inverse are measurable, and Lean proves

```text
Measure.map (canonicalCoord d) (originalTupleVolume d)
  = originalCoordinateVolume d.
```

The tuple-side prior and local bounded-density domination are:

```text
originalTuplePrior d density

(originalTuplePrior d density).restrict s
  <= ENNReal.ofReal K • (originalTupleVolume d).restrict s.
```

The `ENNReal`-valued helper proves

```text
(mu.withDensity f).restrict s <= (C * c) • nu.
```

The real-valued helper proves

```text
(mu.withDensity (fun x => ENNReal.ofReal (density x))).restrict s
  <= (ENNReal.ofReal K * c) • nu.
```

## Proof Shape

The proof composes two elementary measure inequalities:

```text
(mu.withDensity f).restrict s <= C • mu.restrict s
```

from the local a.e. density bound, and

```text
C • mu.restrict s <= C • (c • nu) = (C * c) • nu
```

from the unweighted local domination.

## Nonclaims

This does not transport the original coordinate or tuple measure to an Aoyagi
source edge-family chart. It only names the ambient original measures and
removes smooth-prior boundedness as a separate future source-prior obligation
once Haar/chart transport has been proved or supplied. It proves no
source-image equality, source-rank coverage, normal crossings, pole order, or
RLCT extraction.
