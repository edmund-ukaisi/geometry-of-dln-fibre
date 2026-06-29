# Reproduction - A2 Case 2 Passive Jacobian-Weighted Source-Stratum Bounds Finite Integral

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean work.

## Question

The banked passive Jacobian-weighted local-source finite-integral theorem takes
regular-coordinate loss and density bounds on the retained-passive p.13 local
source:

```text
eventually on nhdsWithin base localSource,
  c * (residualSquareSum(E) + regularSquareSum(u)) <= loss(E,u)
```

Aoyagi's p.13 product-reduction estimate is naturally a source-rank-stratum
statement.  After Theorem 3, the transformed product difference has the block
form

```text
[ C1 - I       -F2
  -F3     prod C^(s) - F3 F2 ],
```

and Aoyagi separates the regular block variables from the reduced product
variables.  In this formalization, that lower bound is represented as an
eventual statement on

```text
nhdsWithin base sourceStratum.
```

The next handoff should therefore keep the passive Jacobian-weighted residual
source package, but allow the regular-coordinate loss and density bounds to
live on the source-rank stratum.

## Calculation

Let

```text
sourceMeasure = passiveMeasure.prod weightedBox
J(z) = retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
jacobianWeightedMeasure = (sourceMeasure.restrict Udom).withDensity (ofReal J)
muJ = Measure.map sourceChart jacobianWeightedMeasure.
```

The already proved passive residual-source theorem gives an open determinant
domain `Udom` and, for this `muJ`, residual hypotheses on the retained-passive
local source:

```text
muJ.restrict localSource-a.e. E,
  0 < residualSquareSum(E)

residualNegPowerIntegrableOn localSource muJ t.
```

The retained-passive local source is locally a chart source around the fixed
base edge family.  The existing coverage theorem supplies an open `Ulocal`
with `base in Ulocal` and

```text
Ulocal inter sourceStratum subset Ulocal inter localSource.
```

Thus the boundary-explicit regular-suspension consumer

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource
```

applies: it restricts the local residual hypotheses from `localSource` to the
final source-rank neighborhood, while using the loss and density bounds from
`nhdsWithin base sourceStratum`.

The resulting finite integral is over

```text
(muJ.restrict (U inter sourceStratum)).prod nu
```

with the same passive Jacobian-weighted source measure `muJ`.

## Lean Target

Add a theorem in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds
```

The theorem should be identical in source-domain construction to the banked
local-source finite-integral handoff, except that its three regular-coordinate
comparison hypotheses are stated over `nhdsWithin base sourceStratum`.

Proof route:

1. Invoke the passive residual-source theorem to construct `Udom` and the
   residual hypotheses for `muJ`.
2. Install `IsFiniteMeasure passiveMeasure` from `hpassive_lt_top` to obtain
   `SFinite muJ`.
3. Obtain the retained-passive local-source coverage open `Ulocal` for
   `Cedge := id`.
4. Prove the retained-passive local source is measurable from `continuous_id`.
5. Apply the source-stratum-bounds/local-source consumer with the residual
   package, `Ulocal`, and the source-stratum loss/density bounds.

## Source Fidelity

Aoyagi pp. 12-13 support the elementary p.13 block display and the separation
of regular variables from the reduced product.  The source does not by itself
state the passive product-domain Jacobian-weighted source measure used here;
that measure is this formalization's local chart-domain packaging of the
retained-passive p.13 coordinates.  Therefore this theorem is a handoff toward
the p.13 regular-variable step, not an original-prior theorem.

## Nonclaims

No external/original source-prior transport, exact localized residual marginal,
determinant-chart Haar pushforward, raw/source Haar theorem, source-image
equality, source-rank coverage, normal-crossing construction, pole order, or
RLCT extraction is proved.

## Kill Conditions

- The retained-passive local-source coverage theorem cannot be instantiated at
  the fixed base edge family with `Cedge = id`.
- The residual-source theorem's local source is not definitionally the one used
  by the source-stratum-bounds consumer.
- `muJ` cannot be made `SFinite` from finite passive mass after restriction,
  density weighting, and source-chart pushforward.
- The source-stratum loss/density hypotheses are not accepted by the
  boundary-explicit consumer without strengthening them to local-source
  hypotheses.
