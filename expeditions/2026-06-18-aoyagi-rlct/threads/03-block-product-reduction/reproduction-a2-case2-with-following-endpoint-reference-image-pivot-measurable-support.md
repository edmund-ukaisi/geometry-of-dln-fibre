# Reproduction - A2 Case 2 with-following endpoint reference image pivot-measurable support

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean implementation.

## Question

Can the endpoint reference image support theorem for the enlarged Case 2 map

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e
```

avoid taking a separate hypothesis that `Y '' Ω` is measurable, when `Ω` is a
measurable subset of the selected-pivot-nonzero locus?

Answer: yes.  The previous A2 rung proves exactly the missing image
measurability under the standard Lusin-Souslin source/target hypotheses.

## Source Calculation

Aoyagi's Case 2 selected-pivot coordinate chart on PDF pp. 19-21 works on the
punctured locus where the chosen successor pivot coordinate is nonzero.  In
the Lean model this condition is

```text
case2PassiveThetaPivotNonzero n hS hnext z.1.
```

For a source set `Ω`, assume:

```text
hΩ : MeasurableSet Ω
hΩpivot : Ω ⊆ {z | case2PassiveThetaPivotNonzero n hS hnext z.1}
```

The previous finite-coordinate theorem gives:

```text
MeasurableSet (Y '' Ω)
```

provided the source has the standard `BorelSpace`/`PolishSpace` hypotheses and
the endpoint topology-tuple target has the standard open-measurable/T2
hypotheses.  This is exactly the missing `himage` input for the already-landed
support theorem:

```text
endpointReferenceImage.restrict (Y '' Ω) = endpointReferenceImage.
```

The unfolded pushforward theorem then follows from the same support theorem:

```text
Measure.map Y (referenceSource.restrict Ω)
  =
endpointReferenceImage.restrict (Y '' Ω).
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

New declarations:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self_of_subset_pivotNonzero
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image_of_subset_pivotNonzero
```

## Reproduction Verdict

This is a valid small A2 support theorem.  It removes a nuisance measurable
image input only on the natural selected-pivot-nonzero source sets.  It does
not strengthen the target measure: the target remains the named endpoint
reference image measure, and the image is still the actual image `Y '' Ω`.

## Kill Conditions

- The new measurable-image theorem must apply to the same endpoint map `Y` used
  in the endpoint reference image measure.
- The source subset hypothesis must be exactly strong enough to put `Ω` inside
  the selected-pivot-nonzero locus.
- The wrapper must preserve the existing source and target regularity
  hypotheses needed by the old support theorem and Lusin-Souslin theorem.

## Nonclaims

No local change-of-variables formula, no Jacobian determinant theorem, no
determinant-chart Haar equality, no raw-Haar transport, no raw-order
composition, no source-image coverage beyond the actual image `Y '' Ω`, no
formal-product domination, no normal crossings, no pole order, and no RLCT
extraction is proved here.
