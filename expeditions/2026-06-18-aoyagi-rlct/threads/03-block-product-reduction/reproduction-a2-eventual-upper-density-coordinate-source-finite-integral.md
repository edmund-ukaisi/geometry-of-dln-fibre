# A2 eventual upper-density coordinate-source finite-integral handoff

Date: 2026-07-03.

## Calculation

The passive-self open coordinate-source handoff returns an open source set
`V` and a continuation:

```text
(forallᵐ z ∂ referenceSource.restrict V, jacobianDensity z <= CJ) ->
(forallᵐ z ∂ baseJ.restrict V, sourceDensity z <= CS) ->
  productResidual positive a.e. and finite negative-power integral
```

The next elementary topological step is to replace those two a.e.
continuations by eventual upper bounds near the base point:

```text
forallᶠ z in nhds z0, jacobianDensity z <= CJ
forallᶠ z in nhds z0, sourceDensity z <= CS.
```

Unfold the two eventual statements as open neighborhoods.  Choose open sets
`HJ` and `HS` such that

```text
z0 in HJ,  forall z in HJ, jacobianDensity z <= CJ,
z0 in HS,  forall z in HS, sourceDensity z <= CS.
```

Given the caller's ambient open set `G`, call the passive-self handoff with

```text
Gdens = G ∩ HJ ∩ HS.
```

The handoff returns an open `V` satisfying

```text
V subset Gdens.
```

Therefore

```text
V subset G,
forall z in V, jacobianDensity z <= CJ,
forall z in V, sourceDensity z <= CS.
```

Because `V` is open, it is measurable.  The pointwise bounds on `V` give
the two a.e. bounds against the restricted measures by `ae_restrict_mem`:

```text
forallᵐ z ∂ referenceSource.restrict V, jacobianDensity z <= CJ,
forallᵐ z ∂ baseJ.restrict V, sourceDensity z <= CS.
```

These are exactly the continuation hypotheses expected by the passive-self
handoff, so the final finite-integral conclusion follows on the same `V`.

## Lean Target

The intended theorem is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_eventually_density_bounds
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

## Boundary

This proves only the same-shrink conversion from eventual upper bounds to the
a.e. upper bounds consumed by the coordinate-source finite-integral handoff.
It does not prove continuity of either density, does not prove the eventual
upper bounds, and does not prove determinant-Haar/raw-Haar transport,
original-prior transport, normal crossings, pole order, or RLCT extraction.
