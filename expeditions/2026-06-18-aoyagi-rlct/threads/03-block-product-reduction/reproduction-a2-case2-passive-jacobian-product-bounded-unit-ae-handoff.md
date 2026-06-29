# Reproduction - A2 Case 2 Passive Jacobian Product Bounded-Unit A.E. Handoff

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before and during Lean.  This is
a measure-domain handoff for an already proved local Jacobian unit, not a
source-prior transport theorem.

## Question

Given the passive Case 2 selected-entry coordinate map

```text
Y z = topologyTuple (retainedData z),
```

and the previously proved local bound

```text
eventually near z0,
  epsilon <= retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
  retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z) <= K,
```

can we turn this into an almost-everywhere statement for the concrete passive
product-domain measure?

Answer: yes.  This uses only the definition of the neighborhood filter and the
elementary fact that a pointwise property on a measurable set holds a.e. after
restricting any measure to that set.

## Domain Measure

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1)
pivotNext = (J + 2, J + 2) in center.
```

The selected-entry signed box and weighted box are

```text
signedBox =
  Measure.pi (fun i : center => volume.restrict (Ioo (-(Rres i)) (Rres i)))

weightedBox =
  signedBox.withDensity
    (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)).
```

For an arbitrary passive measure `passiveMeasure : Measure eta`, the concrete
passive product-domain measure is

```text
sourceMeasure = passiveMeasure.prod weightedBox.
```

No mass-one, support, or positive-mass hypothesis is used.

## Handoff

The local bounded-unit theorem gives positive constants `epsilon`, `K` and an
eventual property in `nhds z0`.  By the definition of `nhds`, choose an open
set

```text
U : Set (eta x (center -> R))
```

with `z0 in U` such that the two-sided bound holds for every `z in U`.  Since
`U` is open, it is measurable under `OpensMeasurableSpace`.  Therefore

```text
ae_restrict_of_forall_mem U.measurableSet
```

turns the pointwise bound on `U` into

```text
for a.e. z with respect to sourceMeasure.restrict U,
  epsilon <= retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
  retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z) <= K.
```

This argument works for any measure on the passive product domain.  The Lean
statement specializes it to the concrete `passiveMeasure.prod weightedBox`
because that is the measure package used in the surrounding Case 2 artifacts.

## New Generic Helper

The reusable helper is

```text
exists_open_ae_restrict_of_eventually_nhds
```

in `LocalMeasureHandoff.lean`.  It is the non-relative analogue of the already
available `exists_open_ae_restrict_inter_of_eventually_nhdsWithin`.

## Nonclaims

- This does not identify an external or original DLN source prior.
- This does not prove determinant-chart Haar transport or raw/source Haar
  transport.
- This does not prove source-image coverage, source-rank coverage, or local
  inverse/coverage.
- This does not prove that `sourceMeasure.restrict U` has positive mass.
- This does not prove that `z0` lies in the support of the weighted box.
- This does not prove normal crossings, pole order, or RLCT.

## Lean Target

The Lean theorem should expose positive constants and an open neighborhood
whose restricted concrete passive product-domain measure sees the bounded-unit
Jacobian factor a.e.:

```text
exists_pos_open_ae_restrict_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure_bounds
```

It should keep determinant-unit hypotheses only at `z0.1`, inherit passive
field continuity from the previous bounded-unit theorem, and add only the
measurability structure needed to form `sourceMeasure.restrict U`.
