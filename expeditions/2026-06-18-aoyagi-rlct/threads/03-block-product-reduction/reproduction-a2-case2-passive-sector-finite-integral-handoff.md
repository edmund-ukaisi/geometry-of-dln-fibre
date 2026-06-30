# Reproduction - A2 Case 2 passive-sector finite-integral handoff

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean.

## Question

The punctured-sector passive selected-entry handoff already proves that, after
shrinking to an open coordinate-domain sector `V` around a base point `z0`, the
chart-produced source measure

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V)
```

is supported on the retained-passive p.13 local source and satisfies the two
residual-source hypotheses:

```text
for mu.restrict localSource-a.e. E,
  0 < squareSum(residualMap E),

residualNegPowerIntegrableOn localSource mu t.
```

Can we feed these two facts directly into the retained-passive p.13 local
finite-integral consumer, keeping the source-data and local loss/density bounds
explicit?

Answer: yes.  This is a pure handoff wrapper.  The selected-entry finite-mass
calculation supplies only the residual-source hypotheses; the p.13 regular
coordinate integral still uses the already proved retained-passive
local-measure theorem.

## Calculation

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1)
pivot  = (J + 2, J + 2)
signedBox = prod_i volume.restrict (-Rres_i, Rres_i)
weightedBox = signedBox.withDensity selectedEntrySourceDensity
sourceMeasure = passiveMeasure.prod weightedBox.
```

The passive-sector theorem gives an open set `V` with `z0 in V`.  For

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData z)

mu = Measure.map sourceChart (sourceMeasure.restrict V),
localSource =
  paperEndpointFixedBaseRetainedPassiveP13LocalSource W2 B2 U0 hU0 id,
```

it proves

```text
mu.restrict localSource = mu,
hpos_local :
  for mu.restrict localSource-a.e. E,
    0 < squareSum(residualMap E),
hbase_local :
  residualNegPowerIntegrableOn id localSource mu t.
```

The retained-passive local-measure consumer needs exactly these two residual
hypotheses, plus:

```text
sourceData at base id,
the retained-passive local-source inclusion near base,
local loss lower bound on the retained-passive local source,
local density nonnegativity and upper bound on the retained-passive local source.
```

For `Cedge = id`, the fixed-base local-source neighborhood theorem supplies an
open set `Ulocal` around

```text
base p = reverseEdge W2 B2 p
```

such that

```text
Ulocal ∩ sourceStratum subset Ulocal ∩ localSource.
```

This is an inclusion on a neighborhood of the fixed-base edge family, not
source-rank coverage and not an image theorem for the chart-produced measure.

Therefore the retained-passive local-measure theorem returns an open set `U`
around `base` and proves

```text
int^- (E,u),
  ofReal
    (indicator_{ball(0,Rreg)}
      ((loss(E,u))^(-(t + regularCount/2)) * density(E,u)) u)
  d ((mu.restrict (U ∩ sourceStratum)).prod nu)
< infinity.
```

## Lean target

Add a wrapper in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

Target name:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass
```

It should call:

```text
exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource
```

## Kill conditions

- Do not claim determinant-chart Haar transport.
- Do not identify an external or original source prior.
- Do not claim source-image equality or source-rank coverage.
- Do not claim an exact localized residual marginal.
- Do not construct normal crossings, compute pole order, or extract RLCT.
- Keep the local loss and density bounds explicit.
