# Review - A2 Case 2 with-following endpoint reference image support

Date: 2026-07-02.

Reviewer: xhigh independent reviewer `Hegel the 2nd`.

## Verdict

PASS.  No findings.

## Checks

The reviewer checked that the new Lean declarations are image-support
bookkeeping only:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image
```

The named endpoint reference image measure is definitionally
`Measure.map Y (referenceSource.restrict Ω)`.  The first theorem restricts it
only to the actual image `Y '' Ω`, and the second theorem unfolds the same
identity against the named measure.  Neither theorem targets determinant-chart
Haar, raw-Haar, raw-order transport, or formal-product measure.

The proof uses the generic support lemma
`measure_map_restrict_image_eq_self_of_aemeasurable` with explicit
measurability hypotheses for `Ω` and `Y '' Ω`.  The reviewer found no
import-cycle risk from importing the source-image helper file.

The reproduction and statement card keep the required boundary: no
determinant-chart Haar equality, no raw-Haar or raw-map transport, no
raw-order composition, no source-image coverage beyond the actual image
`Y '' Ω`, no formal-product domination, no normal crossings, no pole order,
and no RLCT.

## Verification

Reviewer verification:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Controller verification additionally passed focused elaboration, focused
module build, full local `lake build DLNFibre`, no-sorry audit, diff check,
touched-file forbidden-marker scan, and direct axiom probe.
