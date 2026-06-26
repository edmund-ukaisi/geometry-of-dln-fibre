# Statement Card - A2 p.13 left-step local raw-det support

## Declarations

```text
DLNFibre.DLN.Aoyagi.
  p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
DLNFibre.DLN.Aoyagi.
  exists_pos_radius_le_forall_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
DLNFibre.DLN.Aoyagi.
  ae_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet_of_ae_regular_mem_ball
DLNFibre.DLN.Aoyagi.
  exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean
```

## Statement

The actual p.13 left-step raw tuple lies in the raw determinant chart whenever
the regular block `Ctop(u)` has unit determinant.  Since `Ctop(0)=I` and the
determinant is continuous, for every `Rmax > 0` there is `0 < R <= Rmax` such
that every tuple with `u in ball(0,R)` lies in the raw determinant chart.  The
a.e. corollaries turn support in that regular ball into the a.e. chart-domain
hypothesis used by section-image measure identities.

## Role

This removes a local chart-domain support hypothesis for the actual p.13
left-step section.  It keeps the section nature of the map explicit.

## Boundary

No full raw-Haar pushforward, no source/prior transport, no source coverage,
no density identification, no regular-suspension certificate, no normal
crossings, no pole order, and no RLCT.
