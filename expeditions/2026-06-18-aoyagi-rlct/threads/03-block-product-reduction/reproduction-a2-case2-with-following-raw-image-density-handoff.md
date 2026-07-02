# Reproduction - A2 Case 2 with-following raw-image density handoff

Date: 2026-07-02.

Status: pen-and-paper reproduction completed and formalised.  This note does
not claim determinant-chart Haar transport, endpoint Haar transport, raw-order
Haar transport, source-image coverage, a constructed Jacobian density, normal
crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 selected-pivot calculation, PDF pp. 19-21, supplies the
enlarged source coordinates: the passive-theta coordinates together with an
independent following factor.  The local Lean bridge already proves that after
shrinking around a determinant-sector, selected-pivot-nonzero point, the
endpoint topology tuple lands in the retained-passive determinant chart.

On that same shrink, the raw-order map is

```text
rawMap z = topologyTupleEdgeRawOrder (Y z),
```

where `Y` is the enlarged endpoint topology tuple.  Because `Y z` stays in the
determinant chart locally, this raw-order map is continuous on the shrink.

## Calculation

Let `sourceMeasure` be any measure on the enlarged with-following source
domain.  Define

```text
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))

baseJ = sourceMeasure.withDensity jacobianDensity.
```

Suppose a raw-side density

```text
rawDensity : RawTuple -> ENNReal
```

is a.e.-measurable for the actual raw-image measure

```text
Measure.map rawMap (sourceMeasure.restrict V)
```

and that the theta-side density factors through the raw-order map almost
everywhere:

```text
jacobianDensity z = rawDensity (rawMap z)
```

for `sourceMeasure.restrict V`-a.e. `z`.

Restricting `baseJ` to the measurable open set `V` gives

```text
baseJ.restrict V
=
(sourceMeasure.restrict V).withDensity jacobianDensity.
```

The a.e. factorisation rewrites this as

```text
(sourceMeasure.restrict V).withDensity
  (fun z => rawDensity (rawMap z)).
```

Since `rawMap` is a.e.-measurable on `sourceMeasure.restrict V`, the generic
pushforward-with-density identity applies:

```text
Measure.map rawMap
  ((sourceMeasure.restrict V).withDensity
    (fun z => rawDensity (rawMap z)))
=
(Measure.map rawMap (sourceMeasure.restrict V)).withDensity rawDensity.
```

Therefore

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (sourceMeasure.restrict V)).withDensity rawDensity.
```

## Checks

- `sourceMeasure` is arbitrary; no with-following product prior is invented.
- `rawDensity` is supplied and a.e.-measurable; no density construction is
  claimed.
- The conclusion is over the actual raw image of the restricted source
  measure.
- The result is independent of the quiver-based paper and uses only the
  Aoyagi Case 2 coordinate setup plus generic measure bookkeeping.
- xhigh read-only explorer `Beauvoir` independently checked that this is the
  conservative with-following analogue of the passive raw-image theorem and
  that the source-chart density theorem is a sibling/downstream handoff, not an
  input to this raw-image statement.
