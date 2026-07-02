# Review - A2 Case 2 with-following endpoint reference image pivot-measurable support

Date: 2026-07-02.

Reviewer: xhigh read-only subagent `Averroes the 2nd`.

Verdict: PASS.  No findings.

## Scope

Reviewed the two new declarations in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Names:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self_of_subset_pivotNonzero
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image_of_subset_pivotNonzero
```

Also reviewed:

```text
threads/03-block-product-reduction/reproduction-a2-case2-with-following-endpoint-reference-image-pivot-measurable-support.md
threads/03-block-product-reduction/statement-card-a2-case2-with-following-endpoint-reference-image-pivot-measurable-support.md
```

## Checks

The statements match the reproduced slice.  They remove only the separate
`MeasurableSet (Y '' Ω)` hypothesis, replacing it with `hΩ : MeasurableSet Ω`
and `hΩpivot : Ω ⊆ selected-pivot-nonzero`.  The image is definitionally the
same endpoint image `Y '' Ω`, through
`case2PassiveThetaWithFollowingFactorEndpointSectorSet`.

The source measure convention matches the existing
`case2PassiveThetaWithFollowingFactorReferenceSourceMeasure`; no extra source
`MeasurableSpace` instance was introduced.

The proofs are nonvacuous.  The first theorem obtains image measurability from
the selected-pivot-nonzero measurable-image theorem and then invokes the
existing endpoint reference image support theorem.  The second unfolds the
named image measure through that support result.

## Verification

Reviewer reran:

```bash
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

The controller also previously ran focused elaboration, focused module build,
full local `lake build DLNFibre`, no-sorry audit, diff check, touched-file
forbidden-marker scan, and direct axiom probe.  The two new declarations
reported `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No hidden quiver/source dependencies, Haar/Jacobian theorem, raw-map
transport, source-image coverage beyond the actual image `Y '' Ω`, formal
product domination, normal crossings, pole order, or RLCT extraction was found.
