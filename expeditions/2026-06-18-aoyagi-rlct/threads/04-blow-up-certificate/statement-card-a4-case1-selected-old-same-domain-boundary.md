# Statement card - A4 Case 1 selected-old same-domain boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLowerTailExponentPostData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_postData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_levelTailInvariants_postData`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldSuppliedSameDomainBoundary`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldSuppliedSameDomainBoundary.selectedIntroduced`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldSuppliedSameDomainBoundary.selectedLevel`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldSuppliedSameDomainBoundary.sourceMatrix_identity`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldSuppliedSameDomainBoundary.sourceCoordinates_identity`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldSuppliedSameDomainBoundary.updateExponentCertificates`

## Statement

Lean now packages a supplied same-domain boundary for Aoyagi Case 1(1).  The
boundary combines:

- Case 1 first-jump data for the selected old label `(s0,k0)`;
- pre-state exponent certificates over the introduced-label domain `(S,J)`;
- level/least-value and flat-tail invariants;
- supplied post-data saying that only `(s0,k0)` receives the lower-tail
  vector, actual-width numerator increment, and least value `J`.

It exposes two independent projections:

- the Case 1(1) row-wise source-coordinate identity for the selected old
  denominator;
- the same-domain exponent certificate update over `(S,J)`.

## Source Role

This matches the selected-old chart branch on Aoyagi PDF p. 16: the old
exceptional variable `u_(s,k)` itself divides the row strip, and the same
selected label is lowered from `J+J1` to `J`.

## Proved

- A supplied post-data package for the selected old lower-tail exponent update.
- Same-domain exponent-certificate update from that supplied post-data.
- A boundary structure that carries the first-jump, level-tail, pre-certificate,
  and post-data assumptions.
- Projection of the selected old introducedness and selected level.
- Projection of generic and source-coordinate row-strip matrix identities.

## Not Proved

- No construction of the selected old chart or affine atlas.
- No proof that coordinates produce the supplied exponent post-data.
- No domain extension to `(S,J+1)` and no new label `(S,J+1)`.
- No displayed Case 1(2) pivot normalization or `Q/P` identity.
- No chart coverage, regularity, transition regularity, Jacobian, normal
  crossings, RLCT extraction, or transition invariant.
- No type-level identification of the scalar `u` with the source coordinate
  `u_(s0,k0)`.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-same-domain-boundary-a4.md`.
- Review artifact:
  `review-case1-selected-old-same-domain-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
