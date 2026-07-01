# A2 Case 2: finite integral from determinant domination and source-density lower bound

Status: pen-and-paper reproduction checked; Lean wrapper landed.

## Question

The current finite-integral wrapper accepts, on its returned local shrink `V`,
the finite reverse raw-source domination

```text
rawHaar.restrict rawSourceSet
  <= D * Measure.map rawMap (coordinateSourceMeasure.restrict V),
D < infinity.
```

The same-shrink raw/source package now supplies this domination from two
same-shrink hypotheses:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V),
Cdet < infinity,
epsilon <= sourceDensity z
```

for `baseJ.restrict V`-a.e. `z`, with `epsilon` nonzero and finite.

The goal is a finite-integral wrapper whose chart-piece socket asks for these
determinant-side and source-density hypotheses instead of the already-derived
raw-source domination.

## Calculation

Use the direct finite-integral front end that accepts readback domination.
It first returns a source neighborhood `W`, then after the source-image density
bound returns a p.13 source neighborhood `U`.

Inside this same `W`, call the same-shrink raw/source package.  It returns
`V subset W` with:

```text
readback (sourceChart z) = z,
Set.InjOn sourceChart V,
ContinuousOn sourceChart V,
MeasurableSet (sourceChart '' V),
sourceChart '' V subset p13SourceSet,
Measure.map rawChart (Measure.map rawMap (mu.restrict V))
  = Measure.map sourceChart (mu.restrict V),
```

and, from the determinant/source-density hypotheses,

```text
D := Cdet * epsilon^{-1} < infinity,
rawHaar.restrict rawSourceSet
  <= D * Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

For a measurable `chartPiece subset U inter sourceStratum` and
`chartPiece subset sourceChart '' V`, the existing raw-domination readback
calculation gives

```text
AEMeasurable readback (originalVolume.restrict chartPiece),
Measure.map readback (originalVolume.restrict chartPiece)
  <= invHaarScalar * D * coordinateSourceMeasure.restrict W.
```

The `W` appears on the right because the finite front end is formulated over
the larger source neighborhood; `V subset W` gives the measure restriction
monotonicity.

Finally feed this readback domination into the direct original-volume
finite-integral socket.  The scalar is finite because `D < infinity` and the
inverse Haar scalar is finite.

## Lean status

Formalized in
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination`.

The first theorem supplies the same-shrink original-volume readback domination:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

The final finite-integral wrapper is:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

The same-shrink raw/source package was also strengthened to expose
`rawMap z in rawSourceSet` on the shrink and `AEMeasurable rawMap
(coordinateSourceMeasure.restrict V)`, which are exactly the local facts needed
for the determinant-domination handoff.

## Boundary

This wrapper does not prove the determinant-side reverse domination, the lower
bound for `sourceDensity`, determinant-chart Haar transport, exact raw-Haar
pushforward, raw-Haar normalization, source-image coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.

The only analytic citation remains the final normal-crossing-to-RLCT
extraction theorem, not used here.
