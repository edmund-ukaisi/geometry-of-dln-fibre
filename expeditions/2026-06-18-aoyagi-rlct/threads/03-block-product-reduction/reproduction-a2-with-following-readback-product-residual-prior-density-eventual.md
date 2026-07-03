# A2 with-following readback product-residual prior-density eventual bound

## Claim

For the source-cylinder-supported scalar-domination route, an eventual upper
bound for the original-prior density pulled back along the source chart removes
the chart-piece a.e. prior-density hypothesis:

```text
∀ᶠ z in 𝓝 z0, density(sourceChart z) ≤ Kprior.
```

After shrinking the source neighborhood into this event, any chart piece
supported in `sourceChart '' (V ∩ sourceCylinder)` automatically satisfies the
a.e. bound needed by the existing finite-integral wrapper.

## Pen-and-paper check

The existing source-cylinder finite-integral wrapper returns an open local set
`V` and assumes, for each measurable chart piece,

```text
chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder)
```

and

```text
∀ᵐ E ∂ originalVolume.restrict chartPiece, density(E) ≤ Kprior.
```

Assume instead that `density(sourceChart z) ≤ Kprior` holds eventually near
`z0`.  Choose an open set `Gprior` containing `z0` on which this pointwise
bound holds, and run the existing wrapper with `G ∩ Gprior`.  Its returned set
`V` satisfies `V ⊆ Gprior`.

Now let `E ∈ chartPiece`.  The source-cylinder support gives a witness

```text
E = sourceChart z,    z ∈ V ∩ sourceCylinder.
```

Since `V ⊆ Gprior`, the pointwise eventual-bound witness gives

```text
density(E) = density(sourceChart z) ≤ Kprior.
```

Thus the density bound holds pointwise on `chartPiece`.  The helper
`ae_restrict_upper_of_forall_mem` converts this to the a.e. statement for
`originalVolume.restrict chartPiece`, and the existing source-cylinder wrapper
applies.

The continuous-at variant is the same calculation preceded by the standard
topological fact:

```text
ContinuousAt (fun z => density(sourceChart z)) z0
density(sourceChart z0) < Kprior
==> ∀ᶠ z in 𝓝 z0, density(sourceChart z) ≤ Kprior.
```

## Lean target

The landed declarations are:

```text
exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_eventually_priorDensity_comp_sourceChart_upper

exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_chartPiece_subset_sourceChart_image_inter_sourceCylinder_continuousAt_priorDensity_comp_sourceChart_upper
```

This is a bounded-density handoff only.  It does not construct Aoyagi's prior
density, prove its continuity, prove source-cylinder chart-piece support,
prove determinant Haar transport, prove source-image coverage, or extract an
RLCT.
