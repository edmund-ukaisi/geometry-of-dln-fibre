# Statement Card - A2 source-stratum two-sided loss-density iff

Date: 2026-06-29.

## Claim

The local-source supplied-bound p.13 loss-density integrability equivalence
specializes to Aoyagi's source-rank stratum.  Under explicit residual
hypotheses on

```text
paperEndpointFixedBaseSourceRankStratum (K := R) W B Cedge r rEdge
```

and four supplied source-stratum-filter two-sided loss/density bounds, there is
an open base neighborhood `U` such that actual p.13 regular-coordinate
loss-density integrability over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

is equivalent to

```text
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem name:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_sourceStratum_two_sided_bounds
```

## Inputs Kept Explicit

- measurability of the source-rank stratum;
- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`;
- residual square-sum `AEMeasurable` on the restricted source-stratum measure;
- residual square-sum `> 0` a.e. on that measure;
- residual square-sum `<= R^2` a.e. on that measure;
- `0 < R`, `0 < t`, `0 < cL`, `0 < CL`, `0 < dRho`, and `0 <= DRho`;
- four supplied source-stratum-filter comparison bounds, uniform on the
  regular-coordinate ball.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

Independent xhigh review by Bohr the 2nd and Dirac the 2nd passed in
`review-a2-source-stratum-two-sided-loss-density-iff.md`.

`scripts/sorries`, `git diff --check`, the touched-file forbidden-marker scan,
and the direct axiom probe passed.  The axiom footprint for the theorem is
`[propext, Classical.choice, Quot.sound]`.

## Nonclaims

- No proof of comparison or residual hypotheses.
- No p.13 chart construction, chart coverage, source-prior transport,
  Jacobian or density theorem, product-measure transport, original-loss
  identification, normal-crossing, pole-order, or RLCT claim.
