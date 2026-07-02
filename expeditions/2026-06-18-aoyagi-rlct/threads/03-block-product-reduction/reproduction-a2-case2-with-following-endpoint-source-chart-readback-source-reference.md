# Reproduction - A2 Case 2 with-following endpoint source-chart readback source reference

Date: 2026-07-02.

Status: with-following local source-chart readback source-reference theorem
reproduced and formalised.  This note does not claim local `Y` change of
variables, endpoint Haar transport, source-image coverage, raw-map pushforward,
normal crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 calculation, PDF pp. 19-21, supplies a local enlarged source
coordinate chart: passive-theta coordinates together with an independent
following factor.  The Lean source-image layer already proves that near a
determinant-sector point with nonzero selected pivot there is an open set `V`
such that the endpoint source chart

```text
sourceChart z =
  case2PassiveThetaWithFollowingFactorEndpointSourceChart ... z
```

is continuous and injective on `V`, has measurable image `sourceChart '' V`,
and has a readback left inverse:

```text
readback (sourceChart z) = z  for z in V.
```

The present step converts this pointwise local inverse into a measure identity
for the chart-produced source reference.

## Calculation

Let `thetaReference` be any measure on the enlarged theta-coordinate domain.
Define the chart-produced source-image measure

```text
sourceRef =
  Measure.map sourceChart (thetaReference.restrict V).
```

Because `sourceChart` is continuous on the measurable set `V`, it is
a.e.-measurable for `thetaReference.restrict V`.  Because `sourceChart` is
continuous and injective on the Polish measurable coordinate domain, and
`readback (sourceChart z) = z` on `V`, the existing measurable-embedding
adapter gives

```text
AEMeasurable readback sourceRef.
```

Now compute:

```text
Measure.map readback sourceRef
  =
Measure.map readback
  (Measure.map sourceChart (thetaReference.restrict V))
  =
Measure.map (fun z => readback (sourceChart z))
  (thetaReference.restrict V).
```

On the restricted measure, almost every `z` lies in `V`, and the local
left-inverse identity gives

```text
readback (sourceChart z) = z.
```

Therefore

```text
Measure.map readback sourceRef
  =
thetaReference.restrict V.
```

## Checks

- The theorem is for the chart-produced measure only; it does not identify an
  external/original source prior with that measure.
- The local set `V` is produced by the existing with-following source-chart
  image theorem, so it lies inside the prescribed open neighborhood and keeps
  the determinant-chart/readback hypotheses available.
- The result is inverse-measure bookkeeping on the local image.  It does not
  compute a Jacobian or compare to endpoint determinant-chart Haar.

This theorem is a reusable socket for the future local `Y` COV and source
image contracts: once a source-image measure is known to be chart-produced,
the readback recovers the exact theta-domain restriction.
