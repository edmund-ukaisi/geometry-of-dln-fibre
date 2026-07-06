# Reproduction - A2 with-following original-prior residual integrability bridge

Date: 2026-07-06.

Status: Lean target implemented as a downstream residual-integrability wrapper.

## Claim

On the open p.13/readback-preimage patch returned by the with-following
prior-density finite-integral theorem, the original edge-family prior has the
fixed-base p.13 residual negative-power integrability predicate

```text
residualNegPowerIntegrableOn.
```

The wrapper requires the supplied theta-side open set `G` to be contained in
the with-following determinant sector.  It still stops before residual
positivity, adapted-product lower bounds, density comparisons for original
loss, and any `lossDLN` theorem.

## Calculation

The prior-density theorem returns a shrink `V` such that

```text
V subset G,
readback(sourceChart z) = z         for z in V,
sourceChart '' V = p13SourceSet cap readback^{-1}(V),
```

and the readback product-residual negative-power integral is finite over

```text
p13SourceSet cap readback^{-1}(V)
```

for the original edge-family prior.

For a point `E` in this patch, the image equality gives a representation

```text
E = sourceChart z,  z in V.
```

Since `V subset G` and `G` is contained in the determinant sector, the endpoint
retained data of `z` satisfies the determinant-chart hypothesis.  The pointwise
square-sum theorem gives

```text
squareSum(fixedBaseResidual(sourceChart z))
  = squareSum(productResidual(z)).
```

The returned left-inverse identity gives

```text
readback(sourceChart z) = z,
```

so the readback product-residual readout at `sourceChart z` is definitionally
the same product residual.  Therefore, on the patch,

```text
squareSum(fixedBaseResidual E)
  = squareSum(readbackProductResidual E).
```

The generic residual-base adapter turns this pointwise equality plus the finite
readback product-residual integral into `residualNegPowerIntegrableOn`.

## Lean Target

Implemented in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualBridge.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualNegPowerIntegrableOn_originalEdgeFamilyPrior_restrict_p13SourceSet_inter_readback_preimage_isOpen_case2PassiveThetaWithFollowingFactor_of_continuousAt_priorDensity_of_subset_detSector
```

The file is downstream of both the generic product-residual adapter and the
prior-density finite-integral theorem; the generic adapter file remains
independent of the prior-density layer.

## Checks

Xhigh read-only scout `Plato` checked the pointwise equality on the returned
patch and confirmed that no following-factor invertibility, original-loss
comparison, Haar transport, source-rank coverage, normal crossings, pole order,
or RLCT extraction enters this step.  Xhigh read-only scout `McClintock`
checked the API composition and recommended keeping this as a downstream
theorem rather than moving it into the generic adapter file.

## Nonclaims

- No residual positivity theorem.
- No original `lossDLN` finite-integral theorem.
- No adapted-product lower bound or density-bound comparison for original
  loss.
- No source-rank coverage or analytic atlas coverage.
- No statistical prior identification beyond the existing supplied
  `originalEdgeFamilyPrior` object.
- No determinant/raw Haar transport or Jacobian normalization.
- No normal crossings, pole order, or RLCT extraction.
