# A2 Localized Retained-Passive Raw-Order COV

## Purpose

The downstream reverse raw-source theorem currently consumes a determinant-side
domination hypothesis over the whole retained-passive determinant chart.  A
local endpoint patch cannot honestly dominate Haar measure on that whole
global chart.  The determinant side therefore needs a localized raw-order COV:
restrict additive Haar to an arbitrary patch inside the determinant chart, then
push it through the raw-order map with the computed product determinant
density.

## Calculation

Let

```text
Phi = topologyTupleEdgeRawOrder
Sdet = topologyTupleDetChartSet
Omega subset Sdet.
```

On `Sdet`, the existing derivative facts give:

```text
HasFDerivWithinAt Phi (fderiv R Phi z) Omega z
```

for every `z in Omega`, because differentiability holds at every determinant
chart point and `Omega` is a smaller set.  The raw-order map is injective on
`Sdet`, hence injective on `Omega`.

Mathlib's finite-dimensional Jacobian COV then gives, for any additive Haar
measure `m` and null-measurable `Omega`,

```text
map Phi ((m|Omega).withDensity |det D Phi|)
  = m | (Phi '' Omega).
```

The existing retained-passive determinant calculation identifies the solved
`A1` product determinant with the Frechet absolute determinant at every point
of `Sdet`.  Since `Omega subset Sdet`, the two densities are equal
`m|Omega`-a.e.; replacing the density gives:

```text
map Phi ((m|Omega).withDensity formalProductAbsDet)
  = m | (Phi '' Omega).
```

## Boundary

This is determinant-chart infrastructure only.  It does not identify the
endpoint image of the Aoyagi source with Haar measure, does not construct the
endpoint local patch, does not transport source priors or original volume, and
does not prove normal crossings, pole order, or RLCT.

## Verification

Checked on 2026-07-02 in the `expedition/aoyagi-rlct` worktree with local
Lake commands:

```text
cd lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_local_raw_order_axioms.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
scripts/sorries
git diff --check
rg -n "\bsorry\b|\badmit\b|TODO|FIXME|native_decide|#exit|\baxiom\b" \
  lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobianMeasure.lean
```

The focused module and full library builds passed.  `scripts/sorries` reported
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.  The direct axiom probe for the
new theorem reported exactly `[propext, Classical.choice, Quot.sound]`.
