# Statement Card - A2 regular-suspension coordinate map source data

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
paperEndpointFixedBaseRegularBlockCoordinateMap
paperEndpointFixedBaseResidualBlockCoordinateMap
paperEndpointFixedBaseProductDifferenceCoordinateMap
PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt
```

## Statement Shape

The three maps collect the already-defined scalar coordinate values from the
fixed-base canonical product-difference suffix state:

```text
S.Ctop - 1,   -S.B,   lowerLeftBlock S.L
```

for the regular block, `S.D` for the residual block, and the combined cleaned
product-difference coordinate family for both together.

The `PaperEndpointFixedBaseRegularCoordinateSourceData` theorems prove:

```text
map x0 = 0
ContinuousAt map x0
```

for each of the regular, residual, and combined product-difference coordinate
maps.  The proof is componentwise: zero at the base point comes from the
existing scalar centered-coordinate fields, and continuity uses
`continuousAt_pi`.

## Scope

Finite/topological packaging of existing p. 13 scalar coordinate data as
Pi-valued maps.  This is intended as source-data infrastructure for a later
regular-suspension construction.

## Nonclaims

No analytic coordinate chart, local inverse, source-rank openness, analytic
germ-ideal transport, chart coverage, Jacobian/prior compatibility,
normal-crossing construction, pole order, or RLCT extraction is proved.
