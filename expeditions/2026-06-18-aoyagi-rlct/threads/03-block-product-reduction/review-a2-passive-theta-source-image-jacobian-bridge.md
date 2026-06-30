# Review - A2 passive theta source-image Jacobian bridge

Status: controller review after xhigh scout reports from `Halley` and
`Mencius`.

## Soundness Check

The proof consumes only the chart-produced measure

```text
Measure.map sourceChart (baseJ.restrict W).
```

The source-image density bound is transported back to theta coordinates by
`ae_of_ae_map`, so the theorem explicitly assumes the needed a.e.
measurability of `sourceChart`.  The source-image measure is then identified
with the pushforward of the theta-domain `withDensity` measure by the standard
map-with-density formula.  This is exactly the measure consumed by the
existing Jacobian-weighted residual-source theorem.

The statement does not mention arbitrary external measures and does not turn a
source-image density into an original prior.

The finite-integral theorem uses the same rewrite, but delegates the analytic
comparison step to the already-proved theta-domain p.13 finite-integral
wrapper.  It adds no new loss, density, source-stratum, or regular-variable
hypothesis.

## Source Fidelity

This bridge is elementary measure bookkeeping over Aoyagi's local p.13
coordinate setting.  `Mencius` confirmed that passive-theta variables alone do
not represent the full original DLN prior; the missing source-prior theorem
must include the p.13 regular variables.  `Halley` identified this consumer
as the smallest useful non-wrapper bridge downstream of the existing
source-image and Jacobian-measure layers.

## Remaining Boundary

The source-prior frontier is unchanged.  The next genuine theorem must supply
a density identity or transport theorem for the intended local source/original
prior, with the regular p.13 variables included.  The normal-crossing-to-RLCT
extraction remains cited.
