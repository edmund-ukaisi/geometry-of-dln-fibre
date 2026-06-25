# Review - A2 regular-suspension local finite-integral bridge

Date: 2026-06-25.

Reviewer: xhigh subagent Singer the 5th.

Scope:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Lean items reviewed:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top
```

## Findings

No blockers found.

The bridge theorem keeps the promised hypotheses explicit: source
measurability, residual positivity, residual negative-power finiteness, and
uniform-in-fiber loss/density bounds are all assumptions.

The proof correctly restricts to `U ∩ sourceStratum`: it gets `U` from the
source-filter handoff, transfers positivity via `ae_mono`, transfers residual
finiteness via `lintegral_mono'`, then feeds the finite-side p.13 adapter with
base measure `mu.restrict (U ∩ sourceStratum)`.  The adapter's expected shape
matches
`PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top`
in `RegularSuspensionSquareSumIntegrability.lean`.

`residualNegPowerIntegrableOn` is acceptable as a notation wrapper.  The main
caution is that it should not be read as standalone singular-integrability at
zeros; the bridge pairs it with explicit residual positivity, so the current
use is not misleading.

The new import of `RegularSuspensionSquareSumIntegrability` and
`open scoped ENNReal` are appropriate because the theorem depends on the
finite-side adapter and uses `∞`.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

from the `lean/` directory.  The controller also runs the expedition build
script gates before committing.
