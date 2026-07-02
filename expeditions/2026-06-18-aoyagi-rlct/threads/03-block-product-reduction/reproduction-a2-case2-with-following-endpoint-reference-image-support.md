# Reproduction - A2 Case 2 with-following endpoint reference image support

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean implementation.

## Question

For the enlarged Case 2 endpoint map

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e,
```

can the named endpoint reference image measure be restricted to the actual
image `Y '' Ω` without changing it?

Answer: yes, provided `Ω` and `Y '' Ω` are measurable.  This is pure measure
support bookkeeping.  It does not identify the endpoint image measure with
determinant-chart Haar measure, raw-order Haar, or an unrestricted target
measure.

## Source Calculation

Aoyagi's Case 2 calculation on PDF pp. 19-21 builds a selected-pivot source
chart and transports the following factor by the displayed `Q` operation.  In
Lean this source-side endpoint map is the function `Y` above.  The current
reference source measure is already the coordinate-product source measure with
the selected-entry Jacobian density included in the center factor:

```text
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
```

Thus the named endpoint reference image measure is definitionally:

```text
Measure.map Y (referenceSource.restrict Ω).
```

For every `z ∈ Ω`, the image point `Y z` lies in `Y '' Ω`.  Therefore

```text
∀ᵐ z ∂ referenceSource.restrict Ω, Y z ∈ Y '' Ω.
```

If `Y '' Ω` is measurable and `Y` is a.e. measurable for the restricted
source measure, this transfers across `Measure.map Y` and gives:

```text
(Measure.map Y (referenceSource.restrict Ω)).restrict (Y '' Ω)
  =
Measure.map Y (referenceSource.restrict Ω).
```

The required a.e. measurability follows from the existing continuity theorem
for the endpoint topology tuple.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

New declarations:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image
```

## Reproduction Verdict

This is a valid small A2 support theorem.  It names the actual `Y`-image
support of the already-defined endpoint reference image measure.  It is not
the full endpoint-coordinate change-of-variables theorem, because the target
measure is still the endpoint image measure itself.

## Nonclaims

No determinant-chart Haar equality, no raw-Haar transport, no raw-order
composition, no source-image coverage beyond the actual set `Y '' Ω`, no
bounded-density comparison with an external formal-product measure, no normal
crossings, no pole order, and no RLCT extraction is proved here.
