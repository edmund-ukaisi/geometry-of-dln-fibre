# A2 With-Following Formal-Product Source-Cylinder Handoff

Date: 2026-07-07.

## Target

Consume the source-cylinder raw-patch domination theorem at the p.13
formal-product interface.

The intended Lean theorem takes a measurable chart piece satisfying

```text
chartPiece subset sourceChart '' (V inter sourceCylinder)
```

and a lower source-density bound on the same theta shrink, then returns a
finite scalar such that

```text
formalProductMeasure.restrict chartPiece
  <= D * Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

Here

```text
D = Cdet * eps^-1
coordinateSourceMeasure =
  (referenceSource.withDensity jacobianDensity).withDensity sourceDensity.
```

## Pen-And-Paper Reproduction

Aoyagi pp. 10-13 supply the same retained-passive p.13 source-chart algebra
used in the raw-patch handoff.  The elementary calculation is the block
elimination

```text
Q1 A Q2 = [[A1, 0], [0, A4 - A3 A1^{-1} A2]]
```

on a determinant sector, iterated through the product.  In the formal notation
the Lean formalization of that p.13 algebra gives the local source chart and
the compatibility

```text
rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z.
```

The previous raw-patch handoff applies to

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece)
```

and proves

```text
rawHaar.restrict P
  <= (Cdet * eps^-1) *
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

The formal-product socket is a measure-theoretic pushforward wrapper.  It says
that if a p.13 chart piece is supported in the p.13 source set and raw Haar is
dominated on a raw patch containing `rawSourceSet inter rawChart^{-1}
(chartPiece)`, then the formal-product measure restricted to the chart piece
is dominated by the pushforward source reference:

```text
formalProductMeasure.restrict chartPiece
  <= D * Measure.map sourceChart (thetaReference.restrict Vformal).
```

To compose these two facts, choose the formal-product shrink first, then choose
a smaller p.13 source-image shrink, and finally choose the raw-patch shrink
inside it.  The final public support hypothesis remains

```text
chartPiece subset sourceChart '' (V inter sourceCylinder).
```

The p.13 support required by the formal-product socket is not assumed
separately.  It follows internally because the source-image shrink proves

```text
sourceChart '' V subset p13SourceSet.
```

Since `V` is contained in the source-image shrink, source-cylinder support
implies `chartPiece subset sourceChart '' V`, hence
`chartPiece subset p13SourceSet`.

With

```text
thetaReference = coordinateSourceMeasure.restrict V,
```

and `V subset Vformal`, the formal-product socket sees

```text
(thetaReference.restrict Vformal)
  = coordinateSourceMeasure.restrict V.
```

Thus it consumes the raw-patch domination with

```text
D = Cdet * eps^-1
```

and returns the desired formal-product domination on the same final shrink.

## Boundary

This is local measure packaging.  It does not prove determinant-chart Haar
transport, exact raw-Haar pushforward, Haar-scalar normalization,
source-density positivity, source-image coverage beyond the returned local
chart, source-rank coverage, original-prior transport, normal crossings, pole
order, or RLCT extraction.

## Verification

The Lean declaration is:

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_coordinateSourceReference_of_chartPiece_subset_sourceChart_image_inter_sourceCylinder_sourceDensity_lower
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

Passed focused `lake env lean`, targeted module build, local citation audit,
`git diff --check`, `lean/scripts/sorries`, touched-Lean forbidden-marker
scan, direct axiom probe, and direct `#audit_cited` probe.  Xhigh source/API
review found no source-fidelity issue.  Xhigh Lean-boundary review found no
hidden weakening of the source-cylinder hypothesis.
