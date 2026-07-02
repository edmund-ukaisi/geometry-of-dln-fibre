# Statement card - A2 with-following eventual source-density raw domination

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Expected name:

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_eventually_sourceDensity_lower
```

The exported constant is under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

Fix a Case 2 with-following passive-theta base point `z0` in the determinant
sector with nonzero selected pivot, a concrete reference source

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure n hS hnext Rres,
```

and a pullback density

```text
sourceDensity z = sourceImageDensity (sourceChart z).
```

If `sourceDensity` is eventually bounded below by `eps` near `z0`,

```text
forall-eventually z in nhds z0,
  eps <= sourceDensity z,
```

then after shrinking inside any prescribed open neighborhood `G` of `z0`, the
existing determinant-to-raw reverse domination theorem can be used without an
explicit a.e. lower-bound input.

For every additive raw Haar measure, if on the returned `V`:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (referenceSource.restrict V),
```

with `Cdet < infinity` and `eps` nonzero and finite, then:

```text
(Cdet * eps^-1) < infinity
```

and

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * eps^-1) *
       Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

## Proved

The proof extracts an open set `H` from the eventual lower bound, applies the
existing a.e.-lower-bound theorem inside `G inter H`, and then converts the
pointwise lower bound on `V subset H` to:

```text
ae z with respect to baseJ.restrict V, eps <= sourceDensity z.
```

The conversion uses `ae_restrict_mem` and the measurability of the returned
open set `V`.

## Assumed

The determinant-chart reverse domination remains an explicit hypothesis.  The
eventual lower bound remains an explicit hypothesis.

The theorem assumes the usual with-following Case 2 local data and the
standard measurable/topological instances for the with-following source and
retained-passive topology tuple target.

## Cited

None.

## Deferred

No positivity or continuity of `sourceImageDensity` is proved.  No concrete
identification of `sourceImageDensity` is proved.  No determinant-chart Haar
domination/equality, exact raw-Haar pushforward, source-prior/original-prior
transport, p.13 coverage/equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction is proved.

## Status

Proved in Lean.  Focused local module build, full local `lake build
DLNFibre`, no-sorry audit, whitespace check, touched-file marker scan, direct
axiom probe, and xhigh review passed.  The declaration reports
`[propext, Classical.choice, Quot.sound]`.
