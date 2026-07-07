# A2 active-containment rank-cut residual-source bridge

## Object-level calculation

The endpoint-prior rank-cut residual-source bridge previously consumed an
endpoint-reference equality and a determinant-density lower bound.  The active
route uses the support socket

```text
endpointPatch subset activeWriteback '' (activeChart '' (W cap sourceCylinder))
```

for the outer shrink `W`.

For the rank-cut source

```text
rankCutSource = (p13SourceSet cap readback ⁻¹' V) cap sourceStratum,
P = rawSourceSet cap rawChart ⁻¹' rankCutSource,
endpointPatch = rawDetChart cap rawOrderOnEndpoint ⁻¹' P,
```

the same-shrink active prior-readback adapter applied on `W` gives a finite
constant `Cdet` and readback domination into

```text
coordinateSourceMeasure.restrict W.
```

The residual-source theorem works on the inner shrink `V`.  Since the rank-cut
image equality gives

```text
rankCutSource subset sourceChart '' V
```

and `V subset W`, the generic support-sharpening lemma moves the domination
target to

```text
coordinateSourceMeasure.restrict V.
```

That is then exactly the socket required by the rank-cut residual-source
handoff.  The produced-product-positivity wrapper first constructs a positivity
shrink `Vpos` and runs the active bridge inside it.  The strict-density wrapper
fixes `epsilon` and `Kprior` before shrinking, then uses continuity to produce
the a.e. source lower and prior upper bounds on the returned shrink.

## Lean artifacts

The new declarations are:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector

exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_sourceDensity_lower_priorDensity_upper_of_sourceDensity_continuousAt_lt_top_of_continuousAt_priorDensity_of_subset_detSector

exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointPatch_subset_activeWriteback_activeSelectedEntryImage_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

## Boundary

This proves only the active-containment rank-cut residual-source wrappers.  It
does not prove the active containment itself, determinant-chart Haar transport,
raw-order Haar transport, source-prior transport, source-rank or atlas
coverage, normal crossings, pole order, or RLCT extraction.  The strict wrapper
still requires `epsilon != 0`; `epsilon != infinity` is derived from
`epsilon < sourceDensity(z0) < infinity`.
