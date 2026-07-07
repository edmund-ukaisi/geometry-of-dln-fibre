# A2 rank-cut residual-source endpoint-prior readback composition

## Source and role

This is elementary shrink and measure-support bookkeeping for the A2 rank-cut
residual frontier.  It is not a new cited theorem from Aoyagi.  It composes
the same-shrink original-prior readback-domination package with the rank-cut
residual-source readback-nullity wrapper.

## Reproduction

Start with an open determinant-sector neighborhood `G` of `z0`.

The same-shrink prior package returns an outer shrink `W` with

```text
z0 in W,
W subset G,
```

and a continuation: for any measurable `chartPiece subset sourceChart '' W`,
the endpoint-reference identity on `W`, the endpoint lower bound, the
source-density lower bound on `baseJ.restrict W`, and the prior-density upper
bound on `originalVolume.restrict chartPiece` give

```text
AEMeasurable readback (muPrior.restrict chartPiece),
Measure.map readback (muPrior.restrict chartPiece)
  <= Cprior • coordinateSourceMeasure.restrict W.
```

Now run the rank-cut residual-source wrapper inside `W`.  It returns an inner
shrink `V` with

```text
z0 in V,
V subset W,
sourceChart '' V = p13SourceSet cap readback^{-1}(V),
sourceChart '' (V cap rankEq)
  = (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

Set

```text
rankCutSource := (p13SourceSet cap readback^{-1}(V)) cap sourceStratum.
```

The image equality gives

```text
rankCutSource subset sourceChart '' V,
```

and hence, since `V subset W`,

```text
rankCutSource subset sourceChart '' W.
```

Apply the same-shrink prior package with `chartPiece := rankCutSource`.  This
produces readback a.e.-measurability and domination by
`coordinateSourceMeasure.restrict W`.

Finally use the local left inverse

```text
readback(sourceChart z) = z  for z in V
```

and `rankCutSource subset sourceChart '' V` to see that the pushed-forward
restricted prior is supported on `V`.  The support-sharpening lemma then gives
the same scalar domination by `coordinateSourceMeasure.restrict V`.

The rank-cut residual-source readback-nullity wrapper consumes this sharpened
readback domination plus the assumed theta-side product-residual positivity on
`coordinateSourceMeasure.restrict V`, and returns

```text
forall^ae E with respect to muPrior.restrict rankCutSource,
  0 < fixedResidual(E),
residualNegPowerIntegrableOn rankCutSource muPrior t.
```

The scalar finiteness `Cprior < infinity` is inherited from the same-shrink
prior package.

## Kill conditions

- Reading this as proving the endpoint-reference weighted-Haar identity.
- Reading this as proving determinant-chart or raw-order Haar transport.
- Reading this as proving source-prior transport.
- Reading this as proving source-density lower bounds or prior-density upper
  bounds.
- Reading this as proving theta-side product-residual positivity.
- Reading this as proving source-rank or analytic atlas coverage.
- Reading this as proving normal crossings, pole order, or RLCT extraction.

## Lean target

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_endpointReferenceImage_eq_withDensity_formalProductAbsDet_of_one_le_mul_density_sourceDensity_lower_priorDensity_upper_productResidual_pos_ae_of_continuousAt_priorDensity_of_subset_detSector
```

in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean`.

## Verification

Focused `lake env lean` for the touched residual rank-cut bridge passed.
Focused module builds passed for the touched residual rank-cut bridge and the
downstream local-loss rank-cut bridge.  `lean/scripts/sorries`,
`git diff --check`, touched Lean-file marker scan, and direct axiom probe
passed.  The new declaration reports only
`[propext, Classical.choice, Quot.sound]`.
