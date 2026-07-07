# A2 With-Following Source-Cylinder Raw-Patch Handoff

Date: 2026-07-07.

## Target

Expose the source-cylinder endpoint-patch calculation at the raw-order measure
handoff level.

The intended Lean theorem takes a chart piece satisfying

```text
chartPiece subset sourceChart '' (V inter sourceCylinder)
```

and a lower bound for the source density on the same shrink, and returns a
finite scalar such that

```text
rawHaar.restrict (rawSourceSet inter rawChart ⁻¹' chartPiece)
  <= D * Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

Here

```text
coordinateSourceMeasure =
  (referenceSource.withDensity jacobianDensity).withDensity sourceDensity
```

and `D = Cdet * eps^-1`.

## Pen-And-Paper Reproduction

Aoyagi's p.13 chart algebra starts from the elementary block elimination

```text
Q1 A Q2 = [[A1, 0], [0, A4 - A3 A1^{-1} A2]]
```

on the determinant sector where the pivot block is invertible.  Iterating this
block calculation gives the retained-passive p.13 source chart.  In the
formal notation this supplies the local compatibility

```text
rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z
```

on the local determinant/pivot shrink, with `Y z` in the determinant chart and
`rawOrderOnEndpoint (Y z)` in the p.13 raw-source chart.

Let

```text
P = rawSourceSet inter rawChart ⁻¹' chartPiece
Omega_P = rawDetChart inter rawOrderOnEndpoint ⁻¹' P.
```

If `y in Omega_P`, then `rawChart (rawOrderOnEndpoint y)` lies in
`chartPiece`.  Source-cylinder support gives a point `z in V inter
sourceCylinder` such that

```text
sourceChart z = rawChart (rawOrderOnEndpoint y).
```

The p.13 raw-chart map is injective on `rawSourceSet`, and raw order is
injective on `rawDetChart`, so the displayed equality and local compatibility
force

```text
y = Y z.
```

The with-following active selected-entry factorization gives

```text
Y z = activeWriteback (activeChart z).
```

Therefore

```text
Omega_P subset activeWriteback '' (activeChart '' (V inter sourceCylinder)).
```

The existing active-containment raw-patch theorem now gives a finite endpoint
scalar `Cdet` and, after applying the lower source-density bound
`eps <= sourceDensity` on `baseJ.restrict V`, the raw-patch domination

```text
rawHaar.restrict P
  <= (Cdet * eps^-1) *
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

## Boundary

This is still a localized source-cylinder handoff.  It does not prove full
determinant-chart Haar transport, exact raw-Haar pushforward, Haar-scalar
normalization, source-density positivity, source-image coverage, source-rank
coverage, original-prior transport, normal crossings, pole order, or RLCT
extraction.

## Verification

The Lean declaration is:

```text
exists_open_subset_rawHaar_restrict_patch_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Passed focused `lake env lean`, targeted module build, local citation audit,
`git diff --check`, `lean/scripts/sorries`, forbidden-marker scan, direct
axiom probe, and direct `#audit_cited` probe.  Xhigh read-only source and Lean
boundary reviews found no overclaim.
