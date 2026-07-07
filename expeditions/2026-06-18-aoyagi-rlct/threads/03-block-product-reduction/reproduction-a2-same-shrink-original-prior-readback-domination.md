# A2 same-shrink original-prior readback domination

## Source and role

This is elementary measure/source-image bookkeeping attached to the A2
rank-cut residual frontier.  It is not a new cited theorem from Aoyagi.  It
sharpens an already conditional original-prior readback domination result from
the larger returned neighborhood `G` to the actual returned chart shrink `V`.

## Reproduction

Let `chartPiece` be a measurable edge-family source piece with

```text
chartPiece ⊆ sourceChart '' V.
```

Let `μprior` be the original edge-family prior restricted to `chartPiece`.
The existing conditional theorem gives

```text
Measure.map readback μprior
  ≤ Cprior • coordinateSourceMeasure.restrict G.
```

The returned local data also contains

```text
V ⊆ G,
readback(sourceChart z) = z  for z ∈ V.
```

Thus every point of `chartPiece` has the form `sourceChart z` with `z ∈ V`,
and therefore its readback lies in `V`.  Hence the pushed-forward measure is
supported on `V`:

```text
(Measure.map readback μprior).restrict V
  = Measure.map readback μprior.
```

For any measure `ν` supported on `V`, scalar domination

```text
ν ≤ C • coordinateSourceMeasure.restrict G
```

sharpens to

```text
ν ≤ C • (coordinateSourceMeasure.restrict G).restrict V
  = C • coordinateSourceMeasure.restrict V.
```

The last equality uses `V ⊆ G`.

## Kill conditions

- Reading this as proving determinant-chart Haar transport.
- Reading this as proving raw-order Haar transport.
- Reading this as proving original source-prior transport.
- Reading this as proving source-image coverage or source-rank coverage.
- Reading this as proving the source-density lower bound or prior-density
  upper bound used by the conditional theorem.
- Reading this as proving theta-side residual positivity, normal crossings,
  pole order, or RLCT extraction.

## Lean targets

```text
measure_map_restrict_source_subset_image_le_smul_restrict_of_le_smul_restrict_superset

exists_open_subset_originalEdgeFamilyPrior_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_same_shrink_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper
```

in
`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean` and
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean`.

## Verification

Focused `lake env lean` passed for `LocalMeasureHandoff.lean` and for the
determinant-domination file.  Focused module builds passed for
`DLNFibre.DLN.Aoyagi.LocalMeasureHandoff` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination`.
`scripts/sorries`, `git diff --check`, touched Lean-file marker scan, and
direct axiom probes passed.  Both new declarations report only
`[propext, Classical.choice, Quot.sound]`.
