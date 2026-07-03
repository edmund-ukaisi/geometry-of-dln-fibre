# A2 passive-self open coordinate-source finite-integral handoff

Date: 2026-07-03.

## Calculation

The supplied-passive open-patch wrapper already proves the following shape.
Given a passive local set `P`, a finite passive measure, and a domination

```text
passiveRef.restrict P <= Cpassive • passiveMeasure,
```

it constructs an open following patch and then shrinks the with-following
source-chart domain to an open set `V` inside both the passive cylinder and
the following-patch cylinder.  Under the two density continuations

```text
forallᵐ z ∂ referenceSource.restrict V, jacobianDensity z <= CJ,
forallᵐ z ∂ baseJ.restrict V, sourceDensity z <= CS,
```

it returns product-residual positivity almost everywhere and finite
negative-power integrability for the concrete coordinate source measure
restricted to `V`.

The passive-field self-restriction theorem supplies the passive input
internally.  For the base point `z0`, apply

```text
exists_open_passiveLocalSet_case2PassiveThetaPassiveFieldReferenceMeasure_restrict_self_le_smul
```

to the passive-field coordinate `z0.1.1`.  It returns an open measurable set
`P`, a finite measure

```text
passiveMeasure = passiveRef.restrict P,
```

and a scalar `Cpassive = 1` with

```text
passiveRef.restrict P <= Cpassive • passiveMeasure.
```

The only new topology needed for the composition is that the passive-field
cylinder is open in the with-following source domain:

```text
{z | z.1.1 in P}.
```

This is the preimage of `P` under the continuous projection
`z |-> z.1.1`.

Given an ambient open source set `G` containing `z0`, define

```text
Gpassive = G ∩ {z | z.1.1 in P}.
```

Then `Gpassive` is open and contains `z0`.  Feed `Gpassive` to the
supplied-passive wrapper.  The returned local source set satisfies

```text
V subset Gpassive,
```

so it also satisfies both

```text
V subset G,
V subset {z | z.1.1 in P}.
```

The wrapper's passive-domination hypothesis is exactly the self-domination
above.  Since `Cpassive = 1`, the public result records the returned
domination as

```text
passiveRef.restrict P <= 1 • passiveMeasure.
```

No density theorem is proved in this step.  The two remaining inputs are
kept as continuations on the returned `V`, with the measures on which they
must hold stated explicitly.

## Lean Targets

The passive-cylinder topology lemma is:

```text
isOpen_case2PassiveThetaWithFollowingFactor_passiveFieldCylinder
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

The composed handoff is:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_passiveLocalSet_matrixEntryReference_open_followingPatch_open_subset_case2PassiveThetaWithFollowingFactor_coordinateSourceMeasure_productResidual_pos_ae_and_lintegral_rpow_neg_of_density_bounds
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

## Boundary

This closes only the passive coordinate-reference local comparison for the
coordinate-source handoff, by self-restriction.  It proves no
Jacobian-density upper bound, no source-density upper bound, no
determinant-Haar/raw-Haar transport, no original-prior transport, no normal
crossings, pole order, or RLCT extraction.
