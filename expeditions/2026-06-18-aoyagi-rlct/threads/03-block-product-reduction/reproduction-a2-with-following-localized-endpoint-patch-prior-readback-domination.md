# Reproduction - A2 with-following localized endpoint-patch prior readback domination

Status: pen-and-paper reproduction completed and formalized in Lean.

We work inside the localized with-following chart returned by the previous
endpoint-patch readback theorem.  For a measurable p.13 chart piece
`chartPiece` inside the source-chart image, define the raw patch

```text
P = rawSourceSet ∩ rawChart^{-1}(chartPiece)
```

and the determinant endpoint patch

```text
Omega_P = rawDetChart ∩ rawOrderOnEndpoint^{-1}(P).
```

The load-bearing localized volume theorem is

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_endpointPatch_restrict_le_smul_case2PassiveThetaWithFollowingFactor_rawMap_sourceDensity_lower
```

It says that null-measurability of `Omega_P`, endpoint-patch domination on
`Omega_P`, a finite determinant scalar `Cdet`, and a positive finite lower
bound `epsilon` for the source density give

```text
Ddet = Cdet * epsilon^{-1} < infinity
```

and

```text
map readback (originalVolume | chartPiece)
  <= Dvol * (coordinateSourceMeasure | G),

Dvol = ((cHaar^{-1} : NNReal) : ENNReal) * Ddet.
```

Now let the original prior have real density `density` with a local
`originalVolume`-a.e. upper bound

```text
density(E) <= Kprior
```

on `chartPiece`.  The fixed-basis prior definition is

```text
originalPrior = originalVolume.withDensity (ofReal ∘ density).
```

By monotonicity of `ofReal`, the local density bound gives

```text
originalPrior | chartPiece
  <= ofReal(Kprior) * (originalVolume | chartPiece).
```

The readback is a.e. measurable for `originalVolume | chartPiece` by the
localized volume readback theorem.  Since the prior piece is dominated by a
scalar multiple of this volume piece, the same readback map is a.e. measurable
for the prior piece, and pushing the domination forward gives

```text
map readback (originalPrior | chartPiece)
  <= ofReal(Kprior) * map readback (originalVolume | chartPiece).
```

Composing with the localized volume readback domination yields

```text
map readback (originalPrior | chartPiece)
  <= (ofReal(Kprior) * Dvol) * (coordinateSourceMeasure | G).
```

The scalar is finite because `ofReal(Kprior) < infinity`, `Ddet < infinity`,
and the Haar scalar factor is an `NNReal`, hence finite after coercion:

```text
Cprior = ofReal(Kprior) * (((cHaar^{-1} : NNReal) : ENNReal) * Ddet)
       < infinity.
```

This proof uses no global raw-source domination.  The endpoint patch remains
exactly `rawDetChart ∩ rawOrderOnEndpoint^{-1}
(rawSourceSet ∩ rawChart^{-1}(chartPiece))`.

Boundary: this proves only local prior readback domination from an explicit
prior-density upper bound and the existing localized endpoint-patch volume
readback theorem.  It proves no endpoint-Haar transport, source-density
positivity, original source-prior origin, source/image coverage, normal
crossings, pole order, finite-integral socket, or RLCT extraction.
