# Statement card - A2 retained-passive passive-sector construction frontier

Date: 2026-06-30.

## Statement

The current reduced Case 2 selected-entry signed-box chart should not be used
to prove the full retained-passive determinant-chart pushforward hypothesis

```text
m.restrict Sdet = Measure.map chart weightedBox.
```

The next source-moving A2 construction must add the passive retained p.13
coordinates and prove an exact or dominated passive-sector measure theorem.

## Proposed Lean Target

Future module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean
```

Provisional theorem:

```text
measure_map_case2PassiveThetaTopologyTuple_eq_restrict_sectorSet
```

or a finite-scalar domination / bounded-density comparison strong enough for
the local finite-integral consumer.

## Required Data

- A passive-sector coordinate type `Case2PassiveTheta`.
- The selected-entry residual center coordinates.
- Passive retained p.13 coordinates for the determinant chart and the
  existing passive datum fields `A1passive`, `F2`, `A3passive`, `Ctop`, and
  `F3`.
- A sector predicate with pivot nonzero and small-box bounds.
- A map from theta coordinates to retained-passive `TopologyTuple`.
- A product or weighted product measure on theta coordinates.
- An explicit passive unit/Jacobian density, if exact Haar restriction needs
  it.

## Nonclaims

No Lean theorem is proved by this card.  No original source prior,
source-rank coverage, full determinant-chart Haar transport from the reduced
selected-entry section, normal crossings, pole order, or RLCT extraction is
claimed.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-retained-passive-passive-sector-construction.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-retained-passive-passive-sector-construction.md
```
