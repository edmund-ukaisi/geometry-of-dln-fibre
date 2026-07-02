# Statement card - A2 with-following reference-source reverse raw domination

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Name:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

The exported constant is under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

After shrinking inside a prescribed open neighborhood `G` of a Case 2
with-following passive-theta point, specialize the with-following reverse
determinant/raw-order transport theorem to the concrete reference source:

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure n hS hnext Rres.
```

Let:

```text
baseJ = referenceSource.withDensity jacobianDensity
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))
sourceDensity z = sourceImageDensity (sourceChart z)
coordinateSourceMeasure = baseJ.withDensity sourceDensity.
```

If determinant Haar is dominated by the endpoint image:

```text
rawHaar.restrict rawDetChart
  <= Cdet • Measure.map Y (referenceSource.restrict V),
```

and `sourceDensity` is a.e. bounded below by a nonzero finite `eps` with
respect to `baseJ.restrict V`, then:

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * eps^-1) •
       Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

The theorem also returns the scalar finiteness statement:

```text
(Cdet * eps^-1) < infinity.
```

## Proved

The proof first applies the with-following reverse `baseJ` transport theorem
with `sourceMeasure = referenceSource`, obtaining:

```text
rawHaar.restrict rawSourceSet
  <= Cdet • Measure.map rawMap (baseJ.restrict V).
```

It then uses the elementary lower-density handoff:

```text
baseJ.restrict V
  <= eps^-1 • (baseJ.withDensity sourceDensity).restrict V
```

after pushing forward by `rawMap`.  A.e. measurability for
`coordinateSourceMeasure.restrict V` follows from absolute continuity:

```text
(baseJ.withDensity sourceDensity).restrict V << baseJ.restrict V.
```

Finiteness is `ENNReal.mul_lt_top hCdet (ENNReal.inv_lt_top ...)`.

## Assumed

The determinant-chart reverse domination remains an explicit hypothesis.  The
lower bound on `sourceDensity` is also an explicit hypothesis and is stated
with respect to `baseJ.restrict V`.

The theorem assumes the usual local Case 2 with-following data:

- the base point lies in the with-following determinant sector;
- the selected pivot at the base point is nonzero;
- `G` is open and contains the base point;
- the standard finite-dimensional/topological/measurable instances for the
  with-following source and retained-passive topology tuple target.

## Cited

None.

## Deferred

No determinant-chart Haar domination/equality is proved.  No lower bound for
`sourceDensity` is proved.  No exact raw-Haar pushforward, no raw-Haar
normalization, no source-prior/original-prior transport, no p.13 source-image
coverage or equality, no source-rank coverage, no normal crossings, no pole
order, and no RLCT extraction is proved.

## Status

Focused local module build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probe, and xhigh
review passed.  The declaration reports
`[propext, Classical.choice, Quot.sound]`.
