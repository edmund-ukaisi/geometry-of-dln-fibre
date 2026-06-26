# Reproduction - A2 Retained-Passive Monomial-Unit Local-Measure Handoff

Date: 2026-06-26.

Status: reproduced and formalised in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

## Target

The retained-passive signed-box handoff consumes chart-side monomial residual
and source-density bounds.  Existing infrastructure can derive those bounds
from monomial-times-unit identities and unit inequalities.  The target is to
specialize that elementary monomial-unit package to the retained-passive
local source.

## Reproduction

Let

```text
localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W B U0 hU0 Cedge.
```

Assume the same retained-passive local source hypotheses as before:
global `Continuous Cedge`, the self-base equality at `x0`, and a supplied
weighted signed-box pushforward onto `localSource`.

On the signed box, assume the chart-side residual and source density have
monomial-times-unit forms:

```text
residual y =
  residualUnit y * product_i |y_i|^(2 * kres_i)

sourceDensity y =
  densityUnit y * product_i |y_i|^(hres_i).
```

Assume `residualUnit` is bounded below by `cres`, and `densityUnit` is
nonnegative and bounded above by `Cres`, a.e. on the signed box.  The existing
theorem

```text
signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
```

then supplies:

- `AEMeasurable (fun y => ENNReal.ofReal (sourceDensity y))`;
- the monomial residual lower bound;
- source-density nonnegativity;
- the monomial source-density upper bound.

These are exactly the chart-side hypotheses of the retained-passive signed-box
handoff.  Applying that theorem gives the local finite p.13
regular-coordinate integral over a shrunk open neighborhood inside the
source-rank stratum.

## Boundary

This is an elementary chart-side adapter.  It does not construct the source
chart, prove the weighted pushforward identity, prove the monomial-unit
identities, prove the unit bounds, identify a Jacobian density, compare an
original DLN loss, prove normal crossings, determine a pole order, or extract
an RLCT.
