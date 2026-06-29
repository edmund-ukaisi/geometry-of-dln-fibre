# Statement Card - A2 local-source two-sided loss-density iff

Date: 2026-06-29.

## Claim

Under explicit residual hypotheses on a supplied local source and supplied
two-sided source-filter loss/density bounds, there is an open base
neighborhood `U` such that actual p.13 regular-coordinate loss-density
integrability over

```text
(mu.restrict (U inter source)).prod nu
```

is equivalent to residual negative-power integrability on the same restricted
source:

```text
residualNegPowerIntegrableOn Cedge (U inter source) mu t.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Main theorem name:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_localSource_two_sided_bounds
```

## Inputs Kept Explicit

- `MeasurableSet source`;
- `[SFinite nu]` and `[nu.IsAddHaarMeasure]`;
- residual square-sum `AEMeasurable` on `mu.restrict source`;
- residual square-sum `> 0` a.e. on `mu.restrict source`;
- residual square-sum `<= R^2` a.e. on `mu.restrict source`;
- `0 < R`, `0 < t`, `0 < cL`, `0 < CL`, `0 < dRho`, and `0 <= DRho`;
- four supplied source-filter bounds in `nhdsWithin x0 source`, uniform on the
  regular-coordinate ball.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

`scripts/sorries`, `git diff --check`, the touched Lean-file forbidden-marker
scan, and the direct axiom probe passed.  The axiom footprint for the theorem
is `[propext, Classical.choice, Quot.sound]`.

Independent xhigh review passed in
`review-a2-local-source-two-sided-loss-density-iff.md`.

## Nonclaims

- No proof of the comparison or residual hypotheses.
- No chart construction, chart coverage, source-prior transport, Jacobian or
  density theorem, product-measure transport, original-loss identification,
  normal-crossing, pole-order, or RLCT claim.
