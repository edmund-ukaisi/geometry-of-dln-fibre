# Statement Card - A2 retained-passive DetData continuity to a.e. measurability

## Claim

A continuous retained-passive determinant-chart data family supplies the
`AEMeasurable` retained-data hypothesis used by the retained-passive
source-edge-family finite-integral handoffs.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 source-coordinate
construction.  The proof is topological measure bookkeeping: continuous maps
into Borel spaces are measurable, and measurable maps are a.e. measurable.

Lean target:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveDetData_aemeasurable_of_continuous
```

Dependencies:

```text
Continuous.aemeasurable
```

## Nonclaims

No construction of retained data, no determinant-chart proof, no source-image
identity, no residual readout identity, no Jacobian comparison, no finite
integral, no normal crossings, no pole order, and no RLCT.

## Verification

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure` passed.
`scripts/sorries`, `git diff --check`, touched Lean-file forbidden-marker
search, and direct axiom probe passed; the declaration reports only
`[propext, Classical.choice, Quot.sound]`.
