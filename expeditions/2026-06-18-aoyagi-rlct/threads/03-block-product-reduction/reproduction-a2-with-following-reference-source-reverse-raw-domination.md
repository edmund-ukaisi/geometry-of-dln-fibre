# Reproduction - A2 with-following reference-source reverse raw domination

Date: 2026-07-02.

## Scope

This note prepares the concrete with-following reference-source version of the
reverse determinant-to-raw-order transport theorem.

The previous transport theorem is intentionally arbitrary in the source
measure.  The next useful source-side socket should specialize it to the actual
with-following reference source:

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure n hS hnext Rres.
```

It should still keep the determinant-side reverse domination explicit:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (referenceSource.restrict V).
```

The target is reverse raw-source domination by a coordinate source measure:

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * eps^-1) *
      Measure.map rawMap (coordinateSourceMeasure.restrict V),
```

where:

```text
baseJ = referenceSource.withDensity jacobianDensity
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))
sourceDensity z = sourceImageDensity (sourceChart z)
coordinateSourceMeasure = baseJ.withDensity sourceDensity.
```

The theorem should assume the lower source-density bound:

```text
ae z with respect to baseJ.restrict V, eps <= sourceDensity z,
eps != 0,
eps != infinity.
```

## Pen-and-paper calculation

Let:

```text
Phi y = topologyTupleEdgeRawOrder y
formalDensity y =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt y).
```

The with-following reverse transport theorem, applied with
`sourceMeasure = referenceSource`, gives a local open set `V` such that:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (referenceSource.restrict V)
```

implies:

```text
rawHaar.restrict rawSourceSet
  <= Cdet * Measure.map rawMap (baseJ.restrict V).
```

Now compare `baseJ` with:

```text
coordinateSourceMeasure = baseJ.withDensity sourceDensity.
```

Assume:

```text
eps <= sourceDensity z
```

for `baseJ.restrict V` almost every `z`, with `eps` nonzero and finite.  Then
for any measurable target set `A`,

```text
baseJ.restrict V (rawMap^{-1} A)
  <= eps^-1 *
     coordinateSourceMeasure.restrict V (rawMap^{-1} A).
```

Equivalently:

```text
Measure.map rawMap (baseJ.restrict V)
  <= eps^-1 *
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

Composing with the previous raw-source domination gives:

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * eps^-1) *
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

The scalar is finite whenever `Cdet < infinity` and `eps != 0`.

## Boundary

This theorem does not prove the determinant-side reverse domination:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (referenceSource.restrict V).
```

It also does not prove a lower bound for `sourceDensity`, identify
`sourceImageDensity`, prove original/source-prior transport, prove exact
raw-Haar pushforward, prove p.13 coverage or source-rank coverage, construct
normal crossings, compute pole order, or extract RLCT.

## Lean proof plan

Adapt the non-following theorem:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

to the enlarged domain `Case2PassiveThetaWithFollowingFactor`.

The proof should:

1. Apply:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
```

with `sourceMeasure = referenceSource`.

2. Obtain `AEMeasurable rawMap (baseJ.restrict V)` from that theorem.

3. Transfer a.e. measurability to `coordinateSourceMeasure.restrict V` using:

```text
(baseJ.withDensity sourceDensity).restrict V << baseJ.restrict V.
```

4. Apply:

```text
measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
```

with `base = baseJ`, `density = sourceDensity`, and
`target = rawHaar.restrict rawSourceSet`.

5. Use `ENNReal.mul_lt_top` and `ENNReal.inv_lt_top` for scalar finiteness.

No endpoint-reference-image-to-Haar theorem should be introduced or hidden in
this statement.
